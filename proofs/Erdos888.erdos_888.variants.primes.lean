import FormalConjectures.ErdosProblems.«888»

-- Problem: Erdős Problem 888 — primes
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/888.lean:70 (declaration Erdos888.erdos_888.variants.primes)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- Four primes `a ≤ b ≤ c ≤ d` whose product is a square pair up as `a = b` and `c = d`, so in
particular `a * d = b * c`. -/
lemma OMA.prime_square {a b c d : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hsq : IsSquare (a * b * c * d)) :
    a * d = b * c := by
  obtain ⟨s, hs⟩ := hsq
  have h1 : a ∣ s := by
    have h : a ∣ s * s := by
      rw [← hs]
      exact ⟨b * c * d, by ring⟩
    rcases (Nat.Prime.dvd_mul ha).1 h with h | h <;> exact h
  obtain ⟨t, rfl⟩ := h1
  have h2 : b * c * d = a * (t * t) := by
    have h : a * (b * c * d) = a * (a * (t * t)) := by
      rw [show a * (b * c * d) = a * b * c * d by ring, hs]
      ring
    exact Nat.eq_of_mul_eq_mul_left ha.pos h
  have h3 : a ∣ b * c * d := ⟨t * t, h2⟩
  have hab' : a = b := by
    rcases (Nat.Prime.dvd_mul ha).1 h3 with h | h
    · rcases (Nat.Prime.dvd_mul ha).1 h with h | h
      · exact (Nat.prime_dvd_prime_iff_eq ha hb).1 h
      · have := (Nat.prime_dvd_prime_iff_eq ha hc).1 h
        omega
    · have := (Nat.prime_dvd_prime_iff_eq ha hd).1 h
      omega
  subst hab'
  have h4 : c * d = t * t := by
    have h : a * (c * d) = a * (t * t) := by
      rw [← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left ha.pos h
  have h5 : c ∣ t := by
    have h : c ∣ t * t := ⟨d, h4.symm⟩
    rcases (Nat.Prime.dvd_mul hc).1 h with h | h <;> exact h
  obtain ⟨u, rfl⟩ := h5
  have h6 : d = c * (u * u) := by
    have h : c * d = c * (c * (u * u)) := by
      rw [h4]
      ring
    exact Nat.eq_of_mul_eq_mul_left hc.pos h
  have h7 : c = d := (Nat.prime_dvd_prime_iff_eq hc hd).1 ⟨u * u, h6⟩
  rw [h7]

/-- The primes up to `n` satisfy the condition of the problem, so a set of size `π n` exists. -/
lemma OMA.p_primeCounting (n : ℕ) : Erdos888.p n (Nat.primeCounting n) ∧ Nat.primeCounting n ≤ n := by
  have hsub : (Finset.range (n + 1)).filter Nat.Prime ⊆ Finset.Ioc 0 n := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [Finset.mem_Ioc]
    exact ⟨hq.2.pos, by omega⟩
  have hcard : ((Finset.range (n + 1)).filter Nat.Prime).card = Nat.primeCounting n := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  refine ⟨⟨(Finset.range (n + 1)).filter Nat.Prime, ⟨hsub, ?_⟩, hcard⟩, ?_⟩
  · intro a ha b hb c hc d hd hab hbc hcd hsq
    rw [Finset.mem_filter] at ha hb hc hd
    exact OMA.prime_square ha.2 hb.2 hc.2 hd.2 hab hbc hcd hsq
  · have h := Finset.card_le_card hsub
    rw [hcard, Nat.card_Ioc] at h
    omega

/-- Chebyshev's lower bound in the form `n / log n ≤ 4 * π n` for `n ≥ 100`. -/
lemma OMA.chebyshev (n : ℕ) (hn : 100 ≤ n) :
    (n : ℝ) / Real.log n ≤ 4 * (Nat.primeCounting n : ℝ) := by
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hpi := Chebyshev.pi_ge n
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ n / 4 := by
    have hs : Real.log (Real.sqrt ((n : ℝ) + 1)) ≤ Real.sqrt ((n : ℝ) + 1) - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by positivity))
    have h2 : Real.log ((n : ℝ) + 1) = 2 * Real.log (Real.sqrt ((n : ℝ) + 1)) := by
      rw [Real.log_sqrt (by positivity)]
      ring
    have h3 : Real.sqrt ((n : ℝ) + 1) ≤ n / 8 := by
      rw [show (n : ℝ) / 8 = Real.sqrt (((n : ℝ) / 8) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : (n : ℝ) / 4 ≤ n * Real.log 2 - Real.log (n + 1) := by
    have := mul_le_mul_of_nonneg_left hlog2.le (show (0 : ℝ) ≤ n by positivity)
    linarith
  have h5 : (n : ℝ) / 4 / Real.log n ≤ (n * Real.log 2 - Real.log (n + 1)) / Real.log n :=
    div_le_div_of_nonneg_right h4 hlogpos.le
  have h6 : (n : ℝ) / Real.log n = 4 * ((n : ℝ) / 4 / Real.log n) := by
    field_simp
  linarith

theorem OMA.solution : type_of% @Erdos888.erdos_888.variants.primes := by
  refine Asymptotics.IsBigO.of_bound 4 ?_
  rw [Filter.eventually_atTop]
  refine ⟨100, fun n hn => ?_⟩
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  refine le_trans (OMA.chebyshev n hn) (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine Nat.cast_le.2 ?_
  classical
  apply Nat.le_findGreatest
  · exact (OMA.p_primeCounting n).2
  · exact (OMA.p_primeCounting n).1
