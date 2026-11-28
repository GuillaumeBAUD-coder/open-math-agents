import OMAStatements.S_oeis_a131401

-- Problem: A131401: Least number dividing Fibonacci(n) but not dividing Fibonacci(m) for m < n, or 0 if there is no such number.
-- Upstream: formal-conjectures statements/oeis-a131401.lean:0 (declaration OMA.S_oeis_a131401.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- For n = 2 the set is empty, because fib 2 = fib 1, so its infimum is 0. For n = 1 and n >= 3 the number fib n itself lies in the set, since 0 < fib m < fib n for 1 <= m < n; the infimum of a nonempty set of naturals is a member, and 0 is not a member because 0 does not divide fib n > 0.

theorem OMA.solution : type_of% @OMA.S_oeis_a131401.main := by
  intro n hn
  unfold OMA.S_oeis_a131401.a
  constructor
  · intro h
    by_contra hne
    have hmem : Nat.fib n ∈
        {d : ℕ | d ∣ Nat.fib n ∧ ∀ m : ℕ, 1 ≤ m → m < n → ¬ d ∣ Nat.fib m} := by
      refine ⟨dvd_rfl, ?_⟩
      intro m hm1 hmn hdvd
      have hle := Nat.le_of_dvd (Nat.fib_pos.2 (by omega : 0 < m)) hdvd
      have hlt : Nat.fib m < Nat.fib n := by
        by_cases hm : 2 ≤ m
        · have ht := Nat.fib_add_two_strictMono (show m - 2 < n - 2 by omega)
          simpa only [Nat.sub_add_cancel hm, Nat.sub_add_cancel (show 2 ≤ n by omega)] using ht
        · have h3 := Nat.fib_mono (show 3 ≤ n by omega)
          rw [show m = 1 by omega, Nat.fib_one]
          exact (show 1 < Nat.fib 3 by decide).trans_le h3
      omega
    have hs := Nat.sInf_mem ⟨_, hmem⟩
    rw [h] at hs
    have h0 := zero_dvd_iff.1 hs.1
    have hpos : 0 < Nat.fib n := Nat.fib_pos.2 (by omega)
    omega
  · rintro rfl
    have hempty : {d : ℕ | d ∣ Nat.fib 2 ∧ ∀ m : ℕ, 1 ≤ m → m < 2 → ¬ d ∣ Nat.fib m} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro d ⟨hd, hall⟩
      exact hall 1 le_rfl (by decide) (by simpa using hd)
    rw [hempty, Nat.sInf_empty]
