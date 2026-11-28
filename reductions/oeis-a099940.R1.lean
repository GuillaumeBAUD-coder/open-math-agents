import OMAStatements.S_oeis_a099940

-- Reduction oeis-a099940.R1 of A099940: phi(n) * n divides 2 * A056855(n).
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Proved here: pairing each totative k with n - k gives, for n >= 3,
--   2 * A056855(n) = n * R(n),   R(n) = sum over totatives k of the product of the totatives other than k and n - k,
-- so the factor n is automatic and the conjecture is equivalent to phi(n) | R(n). The cases n = 1, 2 are direct.
-- What is left is phi(n) | R(n), split prime by prime: H1 for primes q not dividing n (q is then a totative and the
-- products are rich in factors q), H2 for primes q dividing n (a Leudesdorf-type congruence). Checked for n < 3000.

namespace OMA.R_oeis_a099940_R1

open OMA.S_oeis_a099940

-- phi(n) | R(n) at primes not dividing n.
def H1 : Prop :=
  ∀ n q k : ℕ, 3 ≤ n → q.Prime → ¬ q ∣ n → q ^ k ∣ Nat.totient n →
    q ^ k ∣ ∑ i ∈ totatives n, ∏ j ∈ ((totatives n).erase i).erase (n - i), j

-- phi(n) | R(n) at primes dividing n.
def H2 : Prop :=
  ∀ n q k : ℕ, 3 ≤ n → q.Prime → q ∣ n → q ^ k ∣ Nat.totient n →
    q ^ k ∣ ∑ i ∈ totatives n, ∏ j ∈ ((totatives n).erase i).erase (n - i), j

lemma mem_tot {n k : ℕ} : k ∈ totatives n ↔ 1 ≤ k ∧ k ≤ n ∧ Nat.Coprime k n := by
  unfold totatives
  rw [Finset.mem_filter, Finset.mem_Icc, and_assoc]

lemma lt_of_mem_tot {n k : ℕ} (hn : 2 ≤ n) (hk : k ∈ totatives n) : k < n := by
  obtain ⟨h1, h2, h3⟩ := mem_tot.mp hk
  rcases Nat.lt_or_ge k n with h | h
  · exact h
  · exfalso
    have hkn : k = n := le_antisymm h2 h
    subst hkn
    rw [Nat.coprime_self] at h3
    omega

lemma sub_mem_tot {n k : ℕ} (hn : 2 ≤ n) (hk : k ∈ totatives n) : n - k ∈ totatives n := by
  have hlt := lt_of_mem_tot hn hk
  obtain ⟨h1, h2, h3⟩ := mem_tot.mp hk
  refine mem_tot.mpr ⟨by omega, by omega, ?_⟩
  have : Nat.gcd (n - k) n = Nat.gcd k n := by
    rw [Nat.gcd_comm (n - k) n, Nat.gcd_comm k n, Nat.gcd_self_sub_right (by omega)]
  unfold Nat.Coprime
  rw [this]
  exact h3

lemma ne_sub_of_mem_tot {n k : ℕ} (hn : 3 ≤ n) (hk : k ∈ totatives n) : k ≠ n - k := by
  intro h
  obtain ⟨h1, h2, h3⟩ := mem_tot.mp hk
  have hn2 : n = 2 * k := by omega
  rw [hn2] at h3
  have : Nat.gcd k (2 * k) = k := Nat.gcd_eq_left (Dvd.intro_left 2 rfl)
  unfold Nat.Coprime at h3
  rw [this] at h3
  omega

lemma two_mul_a056855 (n : ℕ) (hn : 3 ≤ n) :
    2 * a056855 n = n * ∑ i ∈ totatives n, ∏ j ∈ ((totatives n).erase i).erase (n - i), j := by
  set T := totatives n with hT
  -- reindex k ↦ n - k
  have hre : ∑ i ∈ T, ∏ j ∈ T.erase i, j = ∑ i ∈ T, ∏ j ∈ T.erase (n - i), j := by
    apply Finset.sum_nbij' (fun i => n - i) (fun i => n - i)
    · intro i hi; exact sub_mem_tot (by omega) hi
    · intro i hi; exact sub_mem_tot (by omega) hi
    · intro i hi
      have := lt_of_mem_tot (by omega) hi
      show n - (n - i) = i
      omega
    · intro i hi
      have := lt_of_mem_tot (by omega) hi
      show n - (n - i) = i
      omega
    · intro i hi
      have := lt_of_mem_tot (by omega) hi
      show ∏ j ∈ T.erase i, j = ∏ j ∈ T.erase (n - (n - i)), j
      rw [show n - (n - i) = i by omega]
  unfold a056855
  rw [← hT, two_mul]
  nth_rewrite 2 [hre]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hlt := lt_of_mem_tot (by omega) hi
  have hne := ne_sub_of_mem_tot hn hi
  have hsub := sub_mem_tot (by omega) hi
  have h1 : n - i ∈ T.erase i := Finset.mem_erase.mpr ⟨fun h => hne h.symm, hsub⟩
  have h2 : i ∈ T.erase (n - i) := Finset.mem_erase.mpr ⟨hne, hi⟩
  rw [← Finset.mul_prod_erase _ _ h1, ← Finset.mul_prod_erase _ _ h2, Finset.erase_right_comm]
  rw [← add_mul]
  congr 1
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a099940.main := by
  intro h1 h2 n hn
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · interval_cases n <;> decide
  · rw [two_mul_a056855 n hn3, mul_comm (Nat.totient n) n]
    apply Nat.mul_dvd_mul_left n
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro q k hq hqk
    by_cases hqn : q ∣ n
    · exact h2 n q k hn3 hq hqn hqk
    · exact h1 n q k hn3 hq hqn hqk

end OMA.R_oeis_a099940_R1
