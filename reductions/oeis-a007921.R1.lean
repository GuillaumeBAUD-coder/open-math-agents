import OMAStatements.S_oeis_a007921

/-!
# Differences of two primes in OEIS A007921

If the difference is odd, the smaller prime must be 2. For a positive even
difference `k`, either `k + 3` or `k + 5` being prime gives an explicit pair.
For the remaining differences, the two primes have the same nonzero residue
modulo 3 when `3 ∣ k`. Otherwise the smaller prime is congruent to `k` modulo 3.
-/

namespace OMA.R_oeis_a007921_R1

open OMA.S_oeis_a007921

/-- Even differences divisible by 3 for which 5 cannot be the smaller prime. -/
def H1 : Prop :=
  ∀ k : ℕ, 0 < k → Even k → 3 ∣ k → ¬ (k + 5).Prime →
    ∃ q : ℕ, 7 ≤ q ∧ q.Prime ∧ (q + k).Prime

/-- Other even differences after excluding 3 and 5 as the smaller prime. -/
def H2 : Prop :=
  ∀ k : ℕ, 0 < k → Even k → ¬ 3 ∣ k → ¬ (k + 3).Prime → ¬ (k + 5).Prime →
    ∃ q : ℕ, 7 ≤ q ∧ q % 3 = k % 3 ∧ q.Prime ∧ (q + k).Prime

/-- An odd positive difference of two primes has smaller prime 2. -/
lemma odd_gap (k : ℕ) (hk : Odd k) : IsPrimeDiff k ↔ (k + 2).Prime := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    have hq2 : q = 2 := by
      rcases hk with ⟨j, hj⟩
      have := hp.eq_two_or_odd
      have := hq.eq_two_or_odd
      have := hq.two_le
      omega
    simpa [hq2, Nat.add_comm] using hp
  · intro hp
    exact ⟨k + 2, 2, hp, Nat.prime_two, Nat.add_comm _ _⟩

private lemma even_gap (h1 : H1) (h2 : H2) (k : ℕ) (hk : 0 < k) (he : Even k) :
    IsPrimeDiff k := by
  by_cases h3 : (k + 3).Prime
  · exact ⟨k + 3, 3, h3, by decide, Nat.add_comm _ _⟩
  by_cases h5 : (k + 5).Prime
  · exact ⟨k + 5, 5, h5, by decide, Nat.add_comm _ _⟩
  by_cases hd : 3 ∣ k
  · obtain ⟨q, _, hq, hp⟩ := h1 k hk he hd h5
    exact ⟨q + k, q, hp, hq, rfl⟩
  · obtain ⟨q, _, _, hq, hp⟩ := h2 k hk he hd h3 h5
    exact ⟨q + k, q, hp, hq, rfl⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007921.main := by
  intro h1 h2 k hk
  rcases k.even_or_odd with he | ho
  · constructor
    · intro h
      exact False.elim (h (even_gap h1 h2 k hk he))
    · intro h
      exact False.elim ((Nat.not_odd_iff_even.mpr he) h.1)
  · constructor
    · intro h
      exact ⟨ho, fun hp => h ((odd_gap k ho).mpr hp)⟩
    · intro h hgap
      exact h.2 ((odd_gap k ho).mp hgap)

private lemma prime_mod_three {p : ℕ} (hp : p.Prime) (h : 3 < p) : p % 3 ≠ 0 := by
  intro hz
  have heq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp
    (Nat.dvd_of_mod_eq_zero hz)
  omega

/-- A solution of the conjecture supplies exactly the witnesses required by both steps. -/
theorem converse (hall : type_of% @OMA.S_oeis_a007921.main) : H1 ∧ H2 := by
  have large_start (k : ℕ) (hk : 0 < k) (he : Even k)
      (h3 : ¬ (k + 3).Prime) (h5 : ¬ (k + 5).Prime) :
      ∃ q : ℕ, 7 ≤ q ∧ q.Prime ∧ (q + k).Prime := by
    have hgap : IsPrimeDiff k := by
      by_contra h
      exact (Nat.not_odd_iff_even.mpr he) ((hall k hk).mp h).1
    obtain ⟨p, q, hp, hq, rfl⟩ := hgap
    refine ⟨q, ?_, hq, hp⟩
    have hn3 : q ≠ 3 := fun h => h3 (by simpa [h, Nat.add_comm] using hp)
    have hn5 : q ≠ 5 := fun h => h5 (by simpa [h, Nat.add_comm] using hp)
    rcases he with ⟨t, ht⟩
    have := hq.eq_two_or_odd
    have := hp.eq_two_or_odd
    have := hq.two_le
    omega
  constructor
  · intro k hk he hd h5
    apply large_start k hk he _ h5
    intro hp
    have hdiv : 3 ∣ k + 3 := by omega
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp hdiv
    omega
  · intro k hk he hd h3 h5
    obtain ⟨q, h7, hq, hp⟩ := large_start k hk he h3 h5
    refine ⟨q, h7, ?_, hq, hp⟩
    have := prime_mod_three hq (by omega)
    have := prime_mod_three hp (by omega)
    omega

end OMA.R_oeis_a007921_R1
