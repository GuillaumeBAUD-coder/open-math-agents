import OMAReductions.R_mo_315770_R1

-- Step mo-315770.R1.H1: hypothesis H1 of reduction mo-315770.R1
-- Credit: @Ciphore
-- For prime powers p^k the divisor sum ∑ 1/(d+1) is never an integer.
-- Case p = 2: exactly one term has an even denominator, so the total cannot
-- be integral.  Case p odd: the sum lies strictly between 0 and 1.

/-- A finite sum of rationals, each expressible as a ratio of integers with odd
denominator, is itself expressible as a ratio of integers with odd denominator. -/
lemma oddDenom_sum (s : Finset ℕ) (g : ℕ → ℚ)
    (h : ∀ i ∈ s, ∃ a b : ℤ, Odd b ∧ g i = (a : ℚ) / (b : ℚ)) :
    ∃ a b : ℤ, Odd b ∧ (∑ i ∈ s, g i) = (a : ℚ) / (b : ℚ) := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact ⟨0, 1, ⟨0, rfl⟩, by simp⟩
  | insert x s hxs ih =>
    obtain ⟨a1, b1, hb1, h1⟩ := h x (Finset.mem_insert_self x s)
    obtain ⟨a2, b2, hb2, h2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨a1 * b2 + a2 * b1, b1 * b2, hb1.mul hb2, ?_⟩
    rw [Finset.sum_insert hxs, h1, h2]
    have oddne : ∀ bb : ℤ, Odd bb → bb ≠ 0 := fun bb hbb => by
      obtain ⟨cc, hcc⟩ := hbb; omega
    have hb1' : (b1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (oddne b1 hb1)
    have hb2' : (b2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (oddne b2 hb2)
    field_simp
    push_cast
    ring

/-- For p ≥ 3 the tail sum of 1/(p^i+1) stays bounded away from 1/2. -/
lemma tail_bound (p : ℕ) (hp3 : 3 ≤ p) (k : ℕ) :
    (∑ i ∈ Finset.range k, (1 : ℚ) / ((p : ℚ) ^ (i + 1) + 1)) ≤
      1 / 2 - 1 / (2 * (p : ℚ) ^ k) := by
  have hpQ : (3 : ℚ) ≤ p := by exact_mod_cast hp3
  have hp_pos : (0 : ℚ) < p := by positivity
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hpk_pos : (0 : ℚ) < (p : ℚ) ^ k := pow_pos hp_pos k
    have hpk1_pos : (0 : ℚ) < (p : ℚ) ^ (k + 1) := pow_pos hp_pos (k + 1)
    have key : (1 : ℚ) / ((p : ℚ) ^ (k + 1) + 1) ≤
        1 / (2 * (p : ℚ) ^ k) - 1 / (2 * (p : ℚ) ^ (k + 1)) := by
      have merge : (1 : ℚ) / (2 * (p : ℚ) ^ k) - 1 / (2 * (p : ℚ) ^ (k + 1)) =
          ((p : ℚ) - 1) / (2 * (p : ℚ) ^ (k + 1)) := by
        have hp2k : (2 : ℚ) * (p : ℚ) ^ k ≠ 0 := by positivity
        have hp2k1 : (2 : ℚ) * (p : ℚ) ^ (k + 1) ≠ 0 := by positivity
        field_simp
        ring
      rw [merge]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have h2p : (2 : ℚ) ≤ (p : ℚ) - 1 := by linarith
      have hpp : (p : ℚ) ^ (k + 1) ≤ (p : ℚ) ^ (k + 1) + 1 := by linarith [hpk1_pos]
      calc (1 : ℚ) * (2 * (p : ℚ) ^ (k + 1))
          = 2 * (p : ℚ) ^ (k + 1) := by ring
        _ ≤ ((p : ℚ) - 1) * ((p : ℚ) ^ (k + 1) + 1) :=
          mul_le_mul h2p hpp (le_of_lt hpk1_pos) (by linarith)
    calc (∑ i ∈ Finset.range k, (1 : ℚ) / ((p : ℚ) ^ (i + 1) + 1)) + 1 / ((p : ℚ) ^ (k + 1) + 1)
        ≤ (1 / 2 - 1 / (2 * (p : ℚ) ^ k)) + (1 / (2 * (p : ℚ) ^ k) - 1 / (2 * (p : ℚ) ^ (k + 1))) := by
          gcongr
      _ = 1 / 2 - 1 / (2 * (p : ℚ) ^ (k + 1)) := by ring

theorem OMA.solution : OMA.R_mo_315770_R1.H1 := by
  intro p k hp z hz
  rw [Nat.divisors_prime_pow hp k, Finset.sum_map] at hz
  simp only [Function.Embedding.coeFn_mk] at hz
  rcases hp.eq_two_or_odd' with rfl | hodd
  · -- p = 2 : every term past the first has odd denominator
    rw [Finset.sum_range_succ'] at hz
    have h0 : (1 : ℚ) / (((2 ^ 0 : ℕ) : ℚ) + 1) = 1 / 2 := by norm_num
    rw [h0] at hz
    obtain ⟨a, b, hb, hTeq⟩ := oddDenom_sum (Finset.range k)
      (fun i => (1 : ℚ) / ((((2 : ℕ) ^ (i + 1) : ℕ) : ℚ) + 1)) (fun i _ => by
        refine ⟨1, (2 : ℤ) ^ (i + 1) + 1, ⟨2 ^ i, by ring⟩, ?_⟩
        push_cast
        rfl)
    rw [hTeq] at hz
    -- hz : a/b + 1/2 = z with b odd — impossible
    obtain ⟨c, hc⟩ := hb
    have hbne0 : b ≠ 0 := by omega
    have hbQ : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hbne0
    have hstep1 : (a : ℚ) / (b : ℚ) = (z : ℚ) - 1 / 2 := by linarith [hz]
    have hstep2 : (a : ℚ) = ((z : ℚ) - 1 / 2) * (b : ℚ) := (div_eq_iff hbQ).mp hstep1
    have h3 : 2 * (a : ℚ) + (b : ℚ) = 2 * ((z : ℚ) * (b : ℚ)) := by linarith [hstep2]
    have hcast : 2 * a + b = 2 * (z * b) := by exact_mod_cast h3
    omega
  · -- p odd, so p ≥ 3 : the sum lies strictly between 0 and 1
    have hp3 : 3 ≤ p := by
      have h2 := hp.two_le
      rcases hodd with ⟨m, hm⟩
      omega
    rw [Finset.sum_range_succ'] at hz
    have h0 : (1 : ℚ) / ((((p : ℕ) ^ 0 : ℕ) : ℚ) + 1) = 1 / 2 := by norm_num
    rw [h0] at hz
    have hposT : (0 : ℚ) ≤ ∑ i ∈ Finset.range k, (1 : ℚ) / ((((p : ℕ) ^ (i + 1) : ℕ) : ℚ) + 1) := by
      apply Finset.sum_nonneg
      intro i _
      positivity
    have hbound := tail_bound p hp3 k
    have hcast_pow : ∀ i : ℕ, ((((p : ℕ) ^ (i + 1)) : ℕ) : ℚ) = (p : ℚ) ^ (i + 1) := by
      intro i; push_cast; rfl
    have hTupper : (∑ i ∈ Finset.range k, (1 : ℚ) / ((((p : ℕ) ^ (i + 1) : ℕ) : ℚ) + 1)) <
        1 / 2 := by
      have heq : (∑ i ∈ Finset.range k, (1 : ℚ) / ((((p : ℕ) ^ (i + 1) : ℕ) : ℚ) + 1)) =
          ∑ i ∈ Finset.range k, (1 : ℚ) / ((p : ℚ) ^ (i + 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hcast_pow i]
      rw [heq]
      have hdiv : (0 : ℚ) < 1 / (2 * (p : ℚ) ^ k) := by positivity
      linarith [hbound]
    have hz0 : (0 : ℚ) < (z : ℚ) := by linarith [hz, hposT]
    have hz1 : (z : ℚ) < 1 := by linarith [hz, hTupper]
    have hz0' : 0 < z := by exact_mod_cast hz0
    have hz1' : z < 1 := by exact_mod_cast hz1
    omega
