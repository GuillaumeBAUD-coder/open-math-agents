import OMAStatements.S_oeis_a129364

open OMA.S_oeis_a129364

/-- `A066841 (n + 1)` as a product over `1 ≤ k ≤ n` of the terms `((n + 1) / k) ^ k`
at the divisors `k` of `n + 1`. -/
theorem bc12_A (n : ℕ) :
    A066841 (n + 1) = ∏ k ∈ Finset.Icc 1 n, (if k ∣ n + 1 then ((n + 1) / k) ^ k else 1) := by
  unfold OMA.S_oeis_a129364.A066841
  have h1 : ∏ d ∈ (n + 1).divisors, d ^ ((n + 1) / d) =
      ∏ d ∈ (n + 1).divisors, ((n + 1) / d) ^ d := by
    rw [← Nat.prod_div_divisors (n + 1) (fun d => d ^ ((n + 1) / d))]
    apply Finset.prod_congr rfl
    intro d hd
    have hdvd : d ∣ n + 1 := Nat.dvd_of_mem_divisors hd
    show ((n + 1) / d) ^ ((n + 1) / ((n + 1) / d)) = ((n + 1) / d) ^ d
    rw [Nat.div_div_self hdvd (by omega)]
  rw [h1]
  have h2 : (n + 1).divisors = (Finset.Icc 1 (n + 1)).filter (fun k => k ∣ n + 1) := by
    ext x
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hx, -⟩
      have hx1 : 0 < x := Nat.pos_of_dvd_of_pos hx (by omega)
      exact ⟨⟨by omega, Nat.le_of_dvd (by omega) hx⟩, hx⟩
    · rintro ⟨-, hx⟩
      exact ⟨hx, by omega⟩
  rw [h2, Finset.prod_filter, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
  rw [if_pos (dvd_refl (n + 1)), Nat.div_self (by omega : 0 < n + 1), one_pow, mul_one]

/-- One step of the factorial form. -/
theorem bc12_step (n k : ℕ) :
    ((n + 1) / k).factorial ^ k =
      (n / k).factorial ^ k * (if k ∣ n + 1 then ((n + 1) / k) ^ k else 1) := by
  by_cases h : k ∣ n + 1
  · rw [if_pos h, Nat.succ_div_of_dvd h, Nat.factorial_succ, mul_pow]
    exact mul_comm _ _
  · rw [if_neg h, Nat.succ_div_of_not_dvd h, mul_one]

/-- The factorial form `a n = ∏_{k=1..n} ((n / k)!)^k`. -/
theorem bc12_fact (n : ℕ) : a n = ∏ k ∈ Finset.Icc 1 n, (n / k).factorial ^ k := by
  induction n with
  | zero =>
    have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
    unfold OMA.S_oeis_a129364.a
    rw [h0, Finset.prod_empty, Finset.prod_empty]
  | succ n ih =>
    have e1 : a (n + 1) = a n * A066841 (n + 1) := by
      unfold OMA.S_oeis_a129364.a
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rw [e1, ih, bc12_A, Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1),
      Nat.div_self (by omega : 0 < n + 1), Nat.factorial_one, one_pow, mul_one,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    rw [bc12_step]

/-- Legendre's formula applied to the factorial form. -/
theorem bc12_lhs (n p : ℕ) (hp : p.Prime) :
    (a n).factorization p =
      ∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / k / p ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  rw [bc12_fact, Nat.factorization_prod (S := Finset.Icc 1 n) (g := fun k => (n / k).factorial ^ k)
    (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _)), Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k _
  show ((n / k).factorial ^ k).factorization p = _
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_def _ hp,
    padicValNat_factorial (show Nat.log p (n / k) < n + 1 from
      Nat.lt_succ_of_le ((Nat.log_le_self p (n / k)).trans (Nat.div_le_self n k)))]

/-- `∑_{k=1..n} k * (N / k) ≤ N * N` when `N ≤ n`. -/
theorem bc12_inner (n N : ℕ) (hN : N ≤ n) : ∑ k ∈ Finset.Icc 1 n, k * (N / k) ≤ N * N := by
  have h1 : ∀ k ∈ Finset.Icc 1 n, k * (N / k) ≤ if k ≤ N then N else 0 := by
    intro k _
    split_ifs with hk
    · exact Nat.mul_div_le N k
    · rw [Nat.div_eq_of_lt (by omega), mul_zero]
  refine (Finset.sum_le_sum h1).trans (le_of_eq ?_)
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have h2 : (Finset.Icc 1 n).filter (fun k => k ≤ N) = Finset.Icc 1 N := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [h2, Nat.card_Icc]
  all_goals simp

theorem bc12_divcomm (n k q : ℕ) : n / k / q = n / q / k := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem bc12_lhs_le (n p : ℕ) (hp : p.Prime) :
    (a n).factorization p ≤ ∑ i ∈ Finset.Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i) := by
  rw [bc12_lhs n p hp]
  have h : ∑ k ∈ Finset.Icc 1 n, k * ∑ i ∈ Finset.Ico 1 (n + 1), n / k / p ^ i =
      ∑ i ∈ Finset.Ico 1 (n + 1), ∑ k ∈ Finset.Icc 1 n, k * (n / p ^ i / k) := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_comm.trans ?_
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [bc12_divcomm]
  rw [h]
  exact Finset.sum_le_sum (fun i _ => bc12_inner n (n / p ^ i) (Nat.div_le_self n _))

/-- The number of multiples of `q` in `[1, n]`. -/
theorem bc12_cnt (n q : ℕ) : ((Finset.Icc 1 n).filter (fun j => q ∣ j)).card = n / q := by
  have h : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div n q

/-- Counting the prime powers dividing both `j` and `k` bounds the valuation of the gcd. -/
theorem bc12_gcd_ge (p j k b : ℕ) (hp : p.Prime) (hj : 0 < j) :
    ∑ i ∈ Finset.Ico 1 b, (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) ≤
      (Nat.gcd j k).factorization p := by
  have hg : Nat.gcd j k ≠ 0 := (Nat.gcd_pos_of_pos_left k hj).ne'
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  calc ((Finset.Ico 1 b).filter (fun i => p ^ i ∣ j ∧ p ^ i ∣ k)).card
      ≤ (Finset.Icc 1 ((Nat.gcd j k).factorization p)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hi ⊢
        exact ⟨hi.1.1, (hp.pow_dvd_iff_le_factorization hg).mp (Nat.dvd_gcd hi.2.1 hi.2.2)⟩
    _ = (Nat.gcd j k).factorization p := by simp

theorem bc12_rhs_ge (n p : ℕ) (hp : p.Prime) :
    ∑ i ∈ Finset.Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i) ≤ (A092287 n).factorization p := by
  have hne : ∀ j ∈ Finset.Icc 1 n, ∏ k ∈ Finset.Icc 1 n, Nat.gcd j k ≠ 0 := by
    intro j hj
    rw [Finset.prod_ne_zero_iff]
    intro k _
    have hj1 : 0 < j := by
      simp only [Finset.mem_Icc] at hj
      omega
    exact (Nat.gcd_pos_of_pos_left k hj1).ne'
  unfold OMA.S_oeis_a129364.A092287
  rw [Nat.factorization_prod (S := Finset.Icc 1 n)
    (g := fun j => ∏ k ∈ Finset.Icc 1 n, Nat.gcd j k) hne, Finsupp.finsetSum_apply]
  have h2 : ∀ j ∈ Finset.Icc 1 n, (∏ k ∈ Finset.Icc 1 n, Nat.gcd j k).factorization p =
      ∑ k ∈ Finset.Icc 1 n, (Nat.gcd j k).factorization p := by
    intro j hj
    have hj1 : 0 < j := by
      simp only [Finset.mem_Icc] at hj
      omega
    rw [Nat.factorization_prod (S := Finset.Icc 1 n) (g := fun k => Nat.gcd j k)
      (fun k _ => (Nat.gcd_pos_of_pos_left k hj1).ne'), Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl h2]
  calc ∑ i ∈ Finset.Ico 1 (n + 1), (n / p ^ i) * (n / p ^ i)
      = ∑ i ∈ Finset.Ico 1 (n + 1), ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n,
          (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        have hrow : ∀ j : ℕ, ∑ k ∈ Finset.Icc 1 n, (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) =
            if p ^ i ∣ j then n / p ^ i else 0 := by
          intro j
          by_cases hj : p ^ i ∣ j
          · rw [if_pos hj]
            simp only [hj, true_and]
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one, bc12_cnt]
          · rw [if_neg hj]
            simp [hj]
        rw [Finset.sum_congr rfl (fun j _ => hrow j), ← Finset.sum_filter, Finset.sum_const,
          smul_eq_mul, bc12_cnt]
    _ = ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 (n + 1),
          (if p ^ i ∣ j ∧ p ^ i ∣ k then 1 else 0) := by
        refine Finset.sum_comm.trans ?_
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ ≤ ∑ j ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (Nat.gcd j k).factorization p := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k _
        have hj1 : 0 < j := by
          simp only [Finset.mem_Icc] at hj
          omega
        exact bc12_gcd_ge p j k (n + 1) hp hj1

theorem OMA.solution : type_of% @OMA.S_oeis_a129364.main := by
  intro n hn
  have ha : a n ≠ 0 := by
    rw [bc12_fact]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hb : A092287 n ≠ 0 := by
    unfold OMA.S_oeis_a129364.A092287
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => Finset.prod_ne_zero_iff.mpr (fun k _ => ?_))
    have hj1 : 0 < j := by
      simp only [Finset.mem_Icc] at hj
      omega
    exact (Nat.gcd_pos_of_pos_left k hj1).ne'
  rw [← Nat.factorization_le_iff_dvd ha hb]
  refine Finsupp.le_def.mpr (fun p => ?_)
  by_cases hp : p.Prime
  · exact (bc12_lhs_le n p hp).trans (bc12_rhs_ge n p hp)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _
