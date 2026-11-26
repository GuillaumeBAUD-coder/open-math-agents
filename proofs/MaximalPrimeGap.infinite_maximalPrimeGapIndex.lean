import FormalConjectures.Wikipedia.MaximalPrimeGap

-- Problem: Shanks's asymptotic conjecture for maximal prime gaps — infinite maximalPrimeGapIndex
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/MaximalPrimeGap.lean:86 (declaration MaximalPrimeGap.infinite_maximalPrimeGapIndex)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- Every value of a sequence of naturals is dominated by the value at some strict record
index: follow the chain of earlier, at-least-as-large values down until it stops. -/
lemma OMA.exists_record_ge (f : ℕ → ℕ) (n : ℕ) :
    ∃ r, (∀ m, m < r → f m < f r) ∧ f n ≤ f r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : ∀ m, m < n → f m < f n
    · exact ⟨n, h, le_refl _⟩
    · push_neg at h
      obtain ⟨m, hm, hle⟩ := h
      obtain ⟨r, hr, hmr⟩ := ih m hm
      exact ⟨r, hr, le_trans hle hmr⟩

/-- An unbounded sequence of naturals has infinitely many strict record indices: finitely many
records would bound every value. -/
lemma OMA.infinite_records (f : ℕ → ℕ) (hf : ∀ N, ∃ n, N < f n) :
    {n : ℕ | ∀ m, m < n → f m < f n}.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := (hfin.image f).bddAbove
  obtain ⟨n, hn⟩ := hf B
  obtain ⟨r, hr, hnr⟩ := OMA.exists_record_ge f n
  have hrB : f r ≤ B := hB (Set.mem_image_of_mem f hr)
  omega

/-- Prime gaps are unbounded: with `M = (N + 1)!`, each of `M + 2, …, M + N + 1` has a proper
divisor, so the first prime that is at least `M + 2` is at least `M + N + 2`, while the prime
just before it is at most `M + 1`. -/
lemma OMA.primeGap_unbounded (N : ℕ) : ∃ n, N < primeGap n := by
  have hMpos : 0 < (N + 1).factorial := Nat.factorial_pos _
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have hex : ∃ k, (N + 1).factorial + 2 ≤ Nat.nth Nat.Prime k :=
    ⟨(N + 1).factorial + 2, hmono.le_apply⟩
  have hk : (N + 1).factorial + 2 ≤ Nat.nth Nat.Prime (Nat.find hex) := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → ¬ ((N + 1).factorial + 2 ≤ Nat.nth Nat.Prime j) :=
    fun j hj => Nat.find_min hex hj
  generalize Nat.find hex = k at hk hmin
  cases k with
  | zero =>
    rw [Nat.nth_prime_zero_eq_two] at hk
    omega
  | succ n =>
    have hlt : ¬ ((N + 1).factorial + 2 ≤ Nat.nth Nat.Prime n) := hmin n (Nat.lt_succ_self n)
    have hprime : (Nat.nth Nat.Prime (n + 1)).Prime := Nat.prime_nth_prime (n + 1)
    have hge : (N + 1).factorial + N + 2 ≤ Nat.nth Nat.Prime (n + 1) := by
      by_contra hcon
      have hj2 : Nat.nth Nat.Prime (n + 1) - (N + 1).factorial ≤ N + 1 := by omega
      have hjpos : 0 < Nat.nth Nat.Prime (n + 1) - (N + 1).factorial := by omega
      have hdvdM : (Nat.nth Nat.Prime (n + 1) - (N + 1).factorial) ∣ (N + 1).factorial :=
        Nat.dvd_factorial hjpos hj2
      have hdvdq : (Nat.nth Nat.Prime (n + 1) - (N + 1).factorial) ∣
          Nat.nth Nat.Prime (n + 1) := by
        have h1 : (Nat.nth Nat.Prime (n + 1) - (N + 1).factorial) ∣
            (N + 1).factorial + (Nat.nth Nat.Prime (n + 1) - (N + 1).factorial) :=
          Dvd.dvd.add hdvdM (dvd_refl _)
        have h2 : (N + 1).factorial + (Nat.nth Nat.Prime (n + 1) - (N + 1).factorial) =
            Nat.nth Nat.Prime (n + 1) := by omega
        rwa [h2] at h1
      rcases (Nat.dvd_prime hprime).mp hdvdq with h | h <;> omega
    refine ⟨n, ?_⟩
    have hgap : primeGap n = Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n := rfl
    rw [hgap]
    omega

theorem OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex := by
  exact OMA.infinite_records primeGap OMA.primeGap_unbounded
