import OMAStatements.S_oeis_a105752

-- Problem oeis-a105752: a(n) = n! * ([n <= 1] + (-1)^n) / 2 equals the sum of the signed Stirling numbers of
-- the first kind s(n, 2k) over k = 0..n.
-- Upstream: statements/oeis-a105752.lean (declaration OMA.S_oeis_a105752.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: the rising factorial P_n(x) = x(x+1)...(x+n-1) has the unsigned Stirling numbers c(n, k) as its
-- coefficients (induction on n, the recurrence of c is multiplication by x + n). Evaluating at 1 and at -1,
--   P_n(1) = n! = E + O   and   P_n(-1) = E - O,
-- where E and O are the sums of c(n, k) over even and odd k. For n >= 2 the factor (x + 1) makes P_n(-1) = 0,
-- so E = n!/2. Finally s(n, 2k) = (-1)^n c(n, 2k), so the sum in the statement is (-1)^n E.
-- The cases n = 0 and n = 1 are checked by computation.

open Polynomial Finset

private lemma stirlingFirst_zero_right_mul_a105752 (j : ℕ) : Nat.stirlingFirst j 0 * j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    have h : Nat.stirlingFirst (j + 1) 0 = 0 := rfl
    rw [h, zero_mul]

private lemma coeff_ascPochhammer_a105752 :
    ∀ j k : ℕ, (ascPochhammer ℤ j).coeff k = (Nat.stirlingFirst j k : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro k
    rw [ascPochhammer_zero, coeff_one]
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ j ih =>
    intro k
    rw [ascPochhammer_succ_right, mul_add, coeff_add, coeff_mul_natCast]
    cases k with
    | zero =>
      have h0 : Nat.stirlingFirst (j + 1) 0 = 0 := rfl
      rw [coeff_mul_X_zero, ih 0, zero_add, h0, ← Nat.cast_mul, stirlingFirst_zero_right_mul_a105752]
    | succ k =>
      rw [coeff_mul_X, ih k, ih (k + 1), Nat.stirlingFirst_succ_succ]
      push_cast
      ring

private lemma sum_even_odd_a105752 (f : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ k ∈ range m, f (2 * k) + ∑ k ∈ range m, f (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, sum_range_succ]
    ring

private lemma eval_neg_one_a105752 (m : ℕ) : (ascPochhammer ℤ (m + 2)).eval (-1) = 0 := by
  have h := ascPochhammer_eval_neg_coe_nat_of_lt (R := ℤ) (n := m + 2) (k := 1) (by omega)
  exact_mod_cast h

theorem OMA.solution : type_of% @OMA.S_oeis_a105752.main := by
  intro n
  rcases n with _ | _ | m
  · decide +kernel
  · decide +kernel
  · obtain ⟨n, hn⟩ : ∃ n, n = m + 1 + 1 := ⟨_, rfl⟩
    rw [← hn]
    have hlt : ¬ n ≤ 1 := by omega
    have e2 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k) = 1 := fun k => by rw [pow_mul]; norm_num
    have o2 : ∀ k : ℕ, (-1 : ℤ) ^ (2 * k + 1) = -1 := fun k => by rw [pow_succ, e2]; norm_num
    have hs : ∀ k : ℕ, OMA.S_oeis_a105752.stirling1 n (2 * k)
        = (-1) ^ n * (Nat.stirlingFirst n (2 * k) : ℤ) := by
      intro k
      unfold OMA.S_oeis_a105752.stirling1
      rcases Nat.lt_or_ge n (2 * k) with h | h
      · rw [Nat.stirlingFirst_eq_zero_of_lt h]
        simp
      · have h' : (-1 : ℤ) ^ n = (-1) ^ (n - 2 * k) * (-1) ^ (2 * k) := by
          rw [← pow_add, Nat.sub_add_cancel h]
        rw [h', e2, mul_one]
    have hdeg : (ascPochhammer ℤ n).natDegree < 2 * (n + 1) := by
      rw [ascPochhammer_natDegree]
      omega
    have h1 := eval_eq_sum_range' hdeg (1 : ℤ)
    have h2 := eval_eq_sum_range' hdeg (-1 : ℤ)
    rw [sum_even_odd_a105752] at h1 h2
    rw [ascPochhammer_eval_one] at h1
    have hm1 : (ascPochhammer ℤ n).eval (-1) = 0 := by
      rw [hn]
      exact eval_neg_one_a105752 m
    rw [hm1] at h2
    simp only [coeff_ascPochhammer_a105752, one_pow, mul_one] at h1
    simp only [coeff_ascPochhammer_a105752, e2, o2, mul_one, mul_neg, sum_neg_distrib] at h2
    have hE : (n.factorial : ℤ) = 2 * ∑ k ∈ range (n + 1), (Nat.stirlingFirst n (2 * k) : ℤ) := by
      linarith
    simp only [hs]
    rw [← mul_sum]
    unfold OMA.S_oeis_a105752.a
    rw [if_neg hlt, zero_add, hE, show ∀ E s : ℤ, 2 * E * s = 2 * (s * E) from fun E s => by ring,
      Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
