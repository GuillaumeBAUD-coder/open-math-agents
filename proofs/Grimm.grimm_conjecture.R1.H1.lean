import OMAReductions.R_Grimm_grimm_conjecture_R1

-- Grimm's conjecture for runs of at most three consecutive composite numbers n, n + 1, n + 2 (n >= 4).
-- For odd n take the least prime factors: neighbours share no prime, and a common prime of n and n + 2 would
-- be 2. For even n one of n, n + 2 is 2 mod 4, hence twice an odd number m >= 3; give it the least prime
-- factor of m (odd), give the other even number the prime 2, and n + 1 its least prime factor (odd).
-- These are trivial small cases, not progress on the conjecture.

namespace OMA.Grimm3

theorem three (n k : ℕ) (hk : k ≤ 3) (p0 p1 p2 : ℕ)
    (h0 : p0.Prime ∧ p0 ∣ n) (h1 : p1.Prime ∧ p1 ∣ n + 1) (h2 : p2.Prime ∧ p2 ∣ n + 2)
    (h01 : p0 ≠ p1) (h02 : p0 ≠ p2) (h12 : p1 ≠ p2) :
    ∃ ps : Fin k ↪ ℕ, ∀ i : Fin k, (ps i).Prime ∧ ps i ∣ (n + i) := by
  refine ⟨⟨fun i => if (i : ℕ) = 0 then p0 else if (i : ℕ) = 1 then p1 else p2, ?_⟩, ?_⟩
  · intro i j hij
    apply Fin.ext
    have hi := i.2
    have hj := j.2
    dsimp only at hij
    split_ifs at hij <;> omega
  · intro i
    have hi := i.2
    show (if (i : ℕ) = 0 then p0 else if (i : ℕ) = 1 then p1 else p2).Prime ∧
      (if (i : ℕ) = 0 then p0 else if (i : ℕ) = 1 then p1 else p2) ∣ n + (i : ℕ)
    split_ifs with ha hb
    · have e : n + (i : ℕ) = n := by omega
      rw [e]
      exact h0
    · have e : n + (i : ℕ) = n + 1 := by omega
      rw [e]
      exact h1
    · have e : n + (i : ℕ) = n + 2 := by omega
      rw [e]
      exact h2

theorem adj (a p : ℕ) (hp : p.Prime) (h1 : p ∣ a) (h2 : p ∣ a + 1) : False := by
  have h := (Nat.dvd_add_right h1).mp h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

theorem gap_two (a p : ℕ) (hp : p.Prime) (h1 : p ∣ a) (h2 : p ∣ a + 2) : p = 2 := by
  have h := (Nat.dvd_add_right h1).mp h2
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h

theorem odd_minFac (m : ℕ) (hm : m % 2 = 1) : m.minFac ≠ 2 := by
  intro h
  have h2 : 2 ∣ m := h ▸ Nat.minFac_dvd m
  omega

theorem small (n k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) (h : ∀ i : Fin k, (n + i).Composite) :
    ∃ ps : Fin k ↪ ℕ, ∀ i : Fin k, (ps i).Prime ∧ ps i ∣ (n + i) := by
  have hc : 1 < n ∧ ¬ n.Prime := h ⟨0, by omega⟩
  have hn4 : 4 ≤ n := by
    rcases hc with ⟨h1, hnp⟩
    by_contra hlt
    have : n = 2 ∨ n = 3 := by omega
    rcases this with rfl | rfl
    · exact hnp Nat.prime_two
    · exact hnp Nat.prime_three
  have hp1 : (n + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hd1 : (n + 1).minFac ∣ n + 1 := Nat.minFac_dvd _
  rcases Nat.even_or_odd n with he | ho
  · have he2 : n % 2 = 0 := Nat.even_iff.mp he
    have h1odd : (n + 1).minFac ≠ 2 := odd_minFac (n + 1) (by omega)
    by_cases h4 : n % 4 = 2
    · -- n = 2 * odd
      have hp0 : (n / 2).minFac.Prime := Nat.minFac_prime (by omega)
      have hd0 : (n / 2).minFac ∣ n := (Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd (by omega))
      have h0odd : (n / 2).minFac ≠ 2 := odd_minFac (n / 2) (by omega)
      refine three n k hk3 (n / 2).minFac (n + 1).minFac 2 ⟨hp0, hd0⟩ ⟨hp1, hd1⟩
        ⟨Nat.prime_two, by omega⟩ ?_ h0odd h1odd
      intro heq
      exact adj n _ hp0 hd0 (heq ▸ hd1)
    · have hp2 : ((n + 2) / 2).minFac.Prime := Nat.minFac_prime (by omega)
      have hd2 : ((n + 2) / 2).minFac ∣ n + 2 :=
        (Nat.minFac_dvd _).trans (Nat.div_dvd_of_dvd (by omega))
      have h2odd : ((n + 2) / 2).minFac ≠ 2 := odd_minFac ((n + 2) / 2) (by omega)
      refine three n k hk3 2 (n + 1).minFac ((n + 2) / 2).minFac ⟨Nat.prime_two, by omega⟩
        ⟨hp1, hd1⟩ ⟨hp2, hd2⟩ (Ne.symm h1odd) (Ne.symm h2odd) ?_
      intro heq
      exact adj (n + 1) _ hp1 hd1 (heq ▸ hd2)
  · have ho2 : n % 2 = 1 := Nat.odd_iff.mp ho
    have hp0 : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hd0 : n.minFac ∣ n := Nat.minFac_dvd _
    have hp2 : (n + 2).minFac.Prime := Nat.minFac_prime (by omega)
    have hd2 : (n + 2).minFac ∣ n + 2 := Nat.minFac_dvd _
    refine three n k hk3 n.minFac (n + 1).minFac (n + 2).minFac ⟨hp0, hd0⟩ ⟨hp1, hd1⟩
      ⟨hp2, hd2⟩ ?_ ?_ ?_
    · intro heq
      exact adj n _ hp0 hd0 (heq ▸ hd1)
    · intro heq
      have h2 := gap_two n _ hp0 hd0 (heq ▸ hd2)
      exact odd_minFac n ho2 h2
    · intro heq
      exact adj (n + 1) _ hp1 hd1 (heq ▸ hd2)

end OMA.Grimm3

theorem OMA.solution : OMA.R_Grimm_grimm_conjecture_R1.H1 := by
  intro n k _ hk hk3 h
  exact OMA.Grimm3.small n k hk hk3 h
