import FormalConjectures.Wikipedia.MaximalPrimeGap

-- Problem: Shanks's asymptotic conjecture for maximal prime gaps — infinite maximalPrimeGapIndex
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/MaximalPrimeGap.lean:86 (declaration MaximalPrimeGap.infinite_maximalPrimeGapIndex)
-- Credit: @jlgmaarav (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open MaximalPrimeGap

/-- None of `(G+1)! + 2, ..., (G+1)! + (G+1)` is prime. -/
lemma not_prime_factorial_add (G j : ℕ) (hj1 : 2 ≤ j) (hj2 : j ≤ G + 1) :
    ¬ ((G + 1).factorial + j).Prime := by
  intro hp
  have hdvd : j ∣ (G + 1).factorial + j :=
    (Nat.dvd_factorial (by omega) hj2).add (dvd_refl j)
  rcases hp.eq_one_or_self_of_dvd j hdvd with h | h
  · omega
  · have := Nat.factorial_pos (G + 1)
    omega

/-- Prime gaps are unbounded. -/
lemma exists_primeGap_gt (G : ℕ) : ∃ n, G < primeGap n := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  set x := (G + 1).factorial + 1 with hx
  set c := Nat.count Nat.Prime (x + 1) with hc
  have hc0 : 0 < c := by
    have h3 : 0 < Nat.count Nat.Prime 3 := by decide
    have := Nat.factorial_pos (G + 1)
    exact lt_of_lt_of_le h3 (Nat.count_monotone _ (by omega))
  refine ⟨c - 1, ?_⟩
  have hlow : Nat.nth Nat.Prime (c - 1) < x + 1 := Nat.nth_lt_of_lt_count (by omega)
  have hhigh : x + 1 ≤ Nat.nth Nat.Prime c := Nat.le_nth_count hinf (x + 1)
  have hprime : (Nat.nth Nat.Prime c).Prime := Nat.nth_mem_of_infinite hinf c
  -- The next prime after `x` is beyond `x + G`.
  have hfar : x + G < Nat.nth Nat.Prime c := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ : ∃ j, Nat.nth Nat.Prime c = (G + 1).factorial + j := ⟨_, (Nat.add_sub_cancel' (by omega)).symm⟩
    exact not_prime_factorial_add G j (by omega) (by omega) (hj ▸ hprime)
  have hsucc : c - 1 + 1 = c := by omega
  unfold primeGap
  rw [hsucc]
  omega

theorem OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro N
  -- The largest gap among the first `N + 1` indices.
  set M := (Finset.range (N + 1)).sup primeGap with hM
  have hex : ∃ n, M < primeGap n := exists_primeGap_gt M
  -- The first index beating `M` is a record index beyond `N`.
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro m hm
    have h1 : ¬ M < primeGap m := Nat.find_min hex hm
    have h2 := Nat.find_spec hex
    omega
  · by_contra hle
    push Not at hle
    have h1 : primeGap (Nat.find hex) ≤ M :=
      Finset.le_sup (f := primeGap) (Finset.mem_range.mpr (by omega))
    have h2 := Nat.find_spec hex
    omega
