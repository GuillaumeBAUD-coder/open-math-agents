import OMAStatements.S_mo_341315

-- Problem: Are there infinitely many primes $p$, positive integers $ k, n $ such that $1 \le n < p$ and $p^k > n.rad(p^{k+1}−n)$?
-- Upstream: formal-conjectures statements/mo-341315.lean:0 (declaration OMA.S_mo_341315.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
Every odd prime p belongs to the set, with n = 1 and k = 2^(p+1) - 1.
For odd p the number p^(2^(s+1)) - 1 is divisible by 2^(s+3) (induction on s).
With s = p write p^(k+1) - 1 = 2^(p+3) * c. This number divides (2c)^(p+3), so its
radical divides 2c. Since p < 2^(p+2), we get
  radical (p^(k+1) - 1) <= 2c < (2^(p+3) * c + 1) / p = p^k.
-/

theorem mo341315_two_adic (p : ℕ) (hp : p % 2 = 1) :
    ∀ s : ℕ, ∃ c : ℕ, p ^ (2 ^ (s + 1)) = 2 ^ (s + 3) * c + 1 := by
  intro s
  induction s with
  | zero =>
    obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := ⟨p / 2, by omega⟩
    obtain ⟨u, hu⟩ : ∃ u, t * (t + 1) = 2 * u := by
      rcases Nat.even_mul_succ_self t with ⟨u, hu⟩
      exact ⟨u, by omega⟩
    refine ⟨u, ?_⟩
    subst ht
    have h : (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    simpa [hu, ← mul_assoc] using h
  | succ s ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨2 ^ (s + 2) * c ^ 2 + c, ?_⟩
    rw [show 2 ^ (s + 1 + 1) = 2 ^ (s + 1) * 2 by ring, pow_mul, hc]
    ring

theorem OMA.solution : type_of% @OMA.S_mo_341315.main := by
  refine Set.Infinite.mono (s := {p : ℕ | p.Prime ∧ p ≠ 2}) ?_ ?_
  · rintro p ⟨hp, hp2⟩
    refine ⟨hp, ?_⟩
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    obtain ⟨c, hc⟩ := mo341315_two_adic p hodd p
    have hp1 : 1 < p := hp.one_lt
    have hcpos : 0 < c := by
      by_contra h
      have h0 : c = 0 := by omega
      subst h0
      have h1 : 1 < p ^ (2 ^ (p + 1)) := Nat.one_lt_pow (by positivity) hp1
      omega
    have h1 : 1 ≤ 2 ^ (p + 1) := Nat.one_le_two_pow
    refine ⟨2 ^ (p + 1) - 1, 1, ?_, le_refl 1, hp1, ?_⟩
    · have h4 : 4 ≤ 2 ^ (p + 1) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · rw [Nat.sub_add_cancel h1, one_mul, hc, Nat.add_sub_cancel]
      have hrad : UniqueFactorizationMonoid.radical (2 ^ (p + 3) * c) ≤ 2 * c := by
        have hdvd : 2 ^ (p + 3) * c ∣ (2 * c) ^ (p + 3) := by
          rw [mul_pow]
          exact mul_dvd_mul_left _ (dvd_pow_self c (by omega))
        have h2c : (2 * c) ^ (p + 3) ≠ 0 := by positivity
        have h := UniqueFactorizationMonoid.radical_dvd_radical hdvd h2c
        rw [UniqueFactorizationMonoid.radical_pow _ (by omega)] at h
        exact Nat.le_of_dvd (by omega) (h.trans UniqueFactorizationMonoid.radical_dvd_self)
      have hpe : p * p ^ (2 ^ (p + 1) - 1) = 2 ^ (p + 3) * c + 1 := by
        rw [← pow_succ', Nat.sub_add_cancel h1, hc]
      have hplt : p < 2 ^ (p + 2) := by
        calc p < 2 ^ p := Nat.lt_two_pow_self
          _ ≤ 2 ^ (p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      by_contra hcon
      have hle : p ^ (2 ^ (p + 1) - 1) ≤ 2 * c := by omega
      have h5 : p * p ^ (2 ^ (p + 1) - 1) ≤ p * (2 * c) := Nat.mul_le_mul_left p hle
      have h6 : p * (2 * c) < 2 ^ (p + 2) * (2 * c) :=
        Nat.mul_lt_mul_of_pos_right hplt (by omega)
      have h7 : 2 ^ (p + 2) * (2 * c) = 2 ^ (p + 3) * c := by ring
      rw [hpe] at h5
      rw [h7] at h6
      omega
  · exact (Nat.infinite_setOfPred_prime.sdiff (Set.finite_singleton 2)).mono
      (fun p hp => ⟨hp.1, by simpa using hp.2⟩)
