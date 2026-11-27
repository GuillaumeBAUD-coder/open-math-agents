import FormalConjectures.ErdosProblems.«683»

-- Problem: Erdős Problem 683 — sylvester schur
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/683.lean:63 (declaration Erdos683.erdos_683.variant.sylvester_schur)
-- Credit: @sebastianbachmaier (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace SylvSchur

lemma keyK (j : ℕ) (hj : 1 ≤ j) : (j + 1) ^ (j + 1) ≤ 4 * j ^ (j + 1) := by
  rcases Nat.lt_or_ge j 3 with h | h
  · interval_cases j <;> norm_num
  · have hjr : (3 : ℝ) ≤ j := by exact_mod_cast h
    have hjpos : (0 : ℝ) < j := by linarith
    have h1 : (1 + 1 / (j : ℝ)) ≤ Real.exp (1 / j) := by
      have := Real.add_one_le_exp (1 / (j : ℝ)); linarith
    have h2 : (1 + 1 / (j : ℝ)) ^ j ≤ Real.exp 1 := by
      calc (1 + 1 / (j : ℝ)) ^ j ≤ (Real.exp (1 / j)) ^ j :=
            pow_le_pow_left₀ (by positivity) h1 j
        _ = Real.exp 1 := by
            rw [← Real.exp_nat_mul]; congr 1; field_simp
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h3 : ((j : ℝ) + 1) ^ j ≤ Real.exp 1 * (j : ℝ) ^ j := by
      have : (1 + 1 / (j : ℝ)) ^ j = ((j : ℝ) + 1) ^ j / (j : ℝ) ^ j := by
        rw [← div_pow]; congr 1; field_simp
      rw [this, div_le_iff₀ (by positivity)] at h2
      linarith
    have h4 : ((j : ℝ) + 1) ^ (j + 1) ≤ 4 * (j : ℝ) ^ (j + 1) := by
      have hjj : (0 : ℝ) ≤ (j : ℝ) ^ j := by positivity
      calc ((j : ℝ) + 1) ^ (j + 1) = ((j : ℝ) + 1) ^ j * ((j : ℝ) + 1) := pow_succ _ _
        _ ≤ (Real.exp 1 * (j : ℝ) ^ j) * ((j : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ ≤ (2.7182818286 * (j : ℝ) ^ j) * ((j : ℝ) + 1) := by gcongr
        _ ≤ 4 * (j : ℝ) ^ (j + 1) := by
            rw [pow_succ]; nlinarith [mul_nonneg hjj (by linarith : (0:ℝ) ≤ (j : ℝ) - 3)]
    exact_mod_cast h4

lemma dvd_choose_of_block {n k p i : ℕ} (hp : p.Prime) (hi : i < k) (hkn : k ≤ n)
    (hpk : k < p) (hdvd : p ∣ n - i) : p ∣ n.choose k := by
  have h1 : p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range]
    exact hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi))
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
  · exact absurd ((Nat.Prime.dvd_factorial hp).1 h) (by omega)
  · exact h

lemma smooth_dvd (m k : ℕ) (hm : m ≠ 0) (h : ∀ p, p.Prime → p ∣ m → p ≤ k) :
    m ∣ (k.factorial) ^ m := by
  rw [← Nat.factorization_le_iff_dvd hm (pow_ne_zero _ (Nat.factorial_ne_zero k))]
  intro p
  rw [Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime ∧ p ∣ m
  · have h1 : 1 ≤ k.factorial.factorization p :=
      hp.1.factorization_pos_of_dvd (Nat.factorial_ne_zero k)
        ((Nat.Prime.dvd_factorial hp.1).2 (h p hp.1 hp.2))
    have h2 : m.factorization p < m := Nat.factorization_lt p hm
    nlinarith
  · have : m.factorization p = 0 := by
      rcases not_and_or.1 hp with h' | h'
      · exact Nat.factorization_eq_zero_of_not_prime m h'
      · exact Nat.factorization_eq_zero_of_not_dvd h'
    rw [this]; exact Nat.zero_le _

lemma direct_ok {n k : ℕ} (hkn : k ≤ n)
    (h : ∃ i < k, ¬ (n - i) ∣ (k.factorial) ^ (n - i)) :
    ∃ p, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  obtain ⟨i, hi, hnd⟩ := h
  have hm : n - i ≠ 0 := by omega
  by_contra hcon
  push_neg at hcon
  apply hnd
  apply smooth_dvd _ _ hm
  intro p hp hpd
  by_contra hlt
  push_neg at hlt
  exact hcon p hp hlt (dvd_choose_of_block hp hi hkn hlt hpd)

lemma P_gt_of_dvd {n k p : ℕ} (hp : p.Prime) (hpk : k < p) (hd : p ∣ n.choose k)
    (hkn : k ≤ n) : Erdos683.P n k > k := by
  unfold Erdos683.P
  have hmem : p ∈ (n.choose k).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hp, hd, (Nat.choose_pos hkn).ne'⟩
  exact lt_of_lt_of_le hpk (Finset.le_sup (f := id) hmem)

lemma ub_A (n k : ℕ) (hn : 0 < n) (hkn : k ≤ n)
    (H : ∀ p, p.Prime → p ∣ n.choose k → p ≤ k) :
    n.choose k ≤ n ^ Nat.primeCounting k := by
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hsub : (n.choose k).primeFactors ⊆ Nat.primesLE k := by
    intro p hp
    rw [Nat.mem_primesLE]
    have := Nat.mem_primeFactors.1 hp
    exact ⟨H p this.1 this.2.1, this.1⟩
  calc n.choose k = ∏ p ∈ (n.choose k).primeFactors, p ^ (n.choose k).factorization p :=
        Nat.prod_primeFactors_pow_factorization hC
    _ ≤ ∏ p ∈ (n.choose k).primeFactors, n :=
        Finset.prod_le_prod' (fun p _ => Nat.pow_factorization_choose_le hn)
    _ = n ^ (n.choose k).primeFactors.card := Finset.prod_const _
    _ ≤ n ^ (Nat.primesLE k).card := Nat.pow_le_pow_right hn (Finset.card_le_card hsub)
    _ = n ^ Nat.primeCounting k := by rw [Nat.primesLE_card_eq_primeCounting]

lemma ub_B (n k t : ℕ) (hn : 0 < n) (hkn : k ≤ n)
    (H : ∀ p, p.Prime → p ∣ n.choose k → p ≤ t) :
    n.choose k ≤ n ^ Nat.primeCounting (Nat.sqrt n) * 4 ^ t := by
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  set C := n.choose k with hCdef
  set s := Nat.sqrt n with hs
  have hprod := Nat.prod_primeFactors_pow_factorization hC
  rw [← Finset.prod_filter_mul_prod_filter_not C.primeFactors (· ≤ s)] at hprod
  have h1 : ∏ p ∈ C.primeFactors with p ≤ s, p ^ C.factorization p ≤
      n ^ Nat.primeCounting s := by
    have hsub : {p ∈ C.primeFactors | p ≤ s} ⊆ Nat.primesLE s := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE]
      exact ⟨hp.2, (Nat.mem_primeFactors.1 hp.1).1⟩
    calc ∏ p ∈ C.primeFactors with p ≤ s, p ^ C.factorization p
        ≤ ∏ p ∈ C.primeFactors with p ≤ s, n :=
          Finset.prod_le_prod' (fun p _ => Nat.pow_factorization_choose_le hn)
      _ = n ^ (C.primeFactors.filter (· ≤ s)).card := Finset.prod_const _
      _ ≤ n ^ (Nat.primesLE s).card := Nat.pow_le_pow_right hn (Finset.card_le_card hsub)
      _ = n ^ Nat.primeCounting s := by rw [Nat.primesLE_card_eq_primeCounting]
  have h2 : ∏ p ∈ C.primeFactors with ¬ p ≤ s, p ^ C.factorization p ≤ primorial t := by
    have hsub : {p ∈ C.primeFactors | ¬ p ≤ s} ⊆ Nat.primesLE t := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Nat.mem_primesLE]
      have := Nat.mem_primeFactors.1 hp.1
      exact ⟨H p this.1 this.2.1, this.1⟩
    calc ∏ p ∈ C.primeFactors with ¬ p ≤ s, p ^ C.factorization p
        ≤ ∏ p ∈ C.primeFactors with ¬ p ≤ s, p := by
          apply Finset.prod_le_prod'
          intro p hp
          rw [Finset.mem_filter] at hp
          have hp1 := (Nat.mem_primeFactors.1 hp.1).1
          have hlarge : n < p ^ 2 := Nat.sqrt_lt'.1 (by omega)
          calc p ^ C.factorization p ≤ p ^ 1 :=
                Nat.pow_le_pow_right hp1.pos (Nat.factorization_choose_le_one hlarge)
            _ = p := pow_one p
      _ ≤ ∏ p ∈ Nat.primesLE t, p := by
          apply Finset.prod_le_prod_of_subset_of_one_le' hsub
          intro p hp _
          exact (Nat.prime_of_mem_primesLE hp).one_lt.le
      _ = primorial t := rfl
  calc C = _ := hprod
    _ ≤ n ^ Nat.primeCounting s * primorial t := Nat.mul_le_mul h1 h2
    _ ≤ n ^ Nat.primeCounting s * 4 ^ t := Nat.mul_le_mul_left _ (primorial_le_four_pow t)


lemma descF_mono (a b : ℕ) (hab : a ≤ b) :
    ∀ k, a.descFactorial k * b ^ k ≤ b.descFactorial k * a ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ]
    have hkey : (a - k) * b ≤ (b - k) * a := by
      rcases le_or_gt k a with h | h
      · obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le h
        obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hab
        have e1 : k + x - k = x := by omega
        have e2 : k + x + y - k = x + y := by omega
        rw [e1, e2]; nlinarith
      · rw [show a - k = 0 by omega]; simp
    calc (a - k) * a.descFactorial k * b ^ (k + 1)
        = ((a - k) * b) * (a.descFactorial k * b ^ k) := by ring
      _ ≤ ((b - k) * a) * (b.descFactorial k * a ^ k) := Nat.mul_le_mul hkey ih
      _ = (b - k) * b.descFactorial k * a ^ (k + 1) := by ring

lemma choose_mono_top (a b k : ℕ) (hab : a ≤ b) :
    a.choose k * b ^ k ≤ b.choose k * a ^ k := by
  have h := descF_mono a b hab k
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose] at h
  have hf : 0 < k.factorial := Nat.factorial_pos k
  have : k.factorial * (a.choose k * b ^ k) ≤ k.factorial * (b.choose k * a ^ k) := by
    calc k.factorial * (a.choose k * b ^ k) = k.factorial * a.choose k * b ^ k := by ring
      _ ≤ k.factorial * b.choose k * a ^ k := h
      _ = k.factorial * (b.choose k * a ^ k) := by ring
  exact Nat.le_of_mul_le_mul_left this hf

lemma lb_A (n k : ℕ) (hkn : k ≤ n) : n ^ k ≤ k ^ k * n.choose k := by
  have h := choose_mono_top k n k hkn
  rw [Nat.choose_self] at h
  linarith

lemma four_pow_le (k : ℕ) (hk : 0 < k) : 4 ^ k ≤ 2 * k * (2 * k).choose k := by
  have := Nat.four_pow_le_two_mul_self_mul_centralBinom k hk
  rwa [Nat.centralBinom_eq_two_mul_choose] at this

lemma lb_B (n k : ℕ) (hk : 0 < k) (h2k : 2 * k ≤ n) :
    4 ^ k * n ^ k ≤ (2 * k) ^ (k + 1) * n.choose k := by
  have h1 := choose_mono_top (2 * k) n k h2k
  have h2 := four_pow_le k hk
  calc 4 ^ k * n ^ k ≤ (2 * k * (2 * k).choose k) * n ^ k := Nat.mul_le_mul_right _ h2
    _ = 2 * k * ((2 * k).choose k * n ^ k) := by ring
    _ ≤ 2 * k * (n.choose k * (2 * k) ^ k) := Nat.mul_le_mul_left _ h1
    _ = (2 * k) ^ (k + 1) * n.choose k := by ring

lemma choose_le_choose_of_le_half (n m k : ℕ) (hmk : m ≤ k) (hk : 2 * k ≤ n) :
    n.choose m ≤ n.choose k := by
  induction k, hmk using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
    have h1 := ih (by omega)
    have h2 : j < n / 2 := by omega
    exact h1.trans (Nat.choose_le_succ_of_lt_half_left h2)

lemma lb_C (n k m : ℕ) (hm : 0 < m) (hmk : m ≤ k) (h2k : 2 * k ≤ n) (h3m : 3 * m ≤ n) :
    6 ^ m ≤ 2 * m * n.choose k := by
  have h1 : (3 * m).choose m ≤ n.choose m := Nat.choose_le_choose m h3m
  have h2 : n.choose m ≤ n.choose k := choose_le_choose_of_le_half n m k hmk h2k
  have h3 := choose_mono_top (2 * m) (3 * m) m (by omega)
  have h4 := four_pow_le m hm
  have hmm : 0 < m ^ m := by positivity
  have h5 : (4 ^ m * 3 ^ m) * m ^ m ≤ (2 * m * (3 * m).choose m * 2 ^ m) * m ^ m := by
    calc (4 ^ m * 3 ^ m) * m ^ m = 4 ^ m * (3 * m) ^ m := by rw [mul_pow]; ring
      _ ≤ (2 * m * (2 * m).choose m) * (3 * m) ^ m := Nat.mul_le_mul_right _ h4
      _ = 2 * m * ((2 * m).choose m * (3 * m) ^ m) := by ring
      _ ≤ 2 * m * ((3 * m).choose m * (2 * m) ^ m) := Nat.mul_le_mul_left _ h3
      _ = (2 * m * (3 * m).choose m * 2 ^ m) * m ^ m := by rw [mul_pow]; ring
  have h6 := Nat.le_of_mul_le_mul_right h5 hmm
  have h7 : 6 ^ m * 2 ^ m ≤ (2 * m * (3 * m).choose m) * 2 ^ m := by
    calc 6 ^ m * 2 ^ m = 4 ^ m * 3 ^ m := by rw [← mul_pow, ← mul_pow]; norm_num
      _ ≤ _ := h6
  have h8 := Nat.le_of_mul_le_mul_right h7 (by positivity)
  calc 6 ^ m ≤ 2 * m * (3 * m).choose m := h8
    _ ≤ 2 * m * n.choose k := Nat.mul_le_mul_left _ (h1.trans h2)

lemma pi_bound (m : ℕ) : 3 * Nat.primeCounting m ≤ m + 9 := by
  rcases Nat.lt_or_ge m 6 with h | h
  · have : Nat.primeCounting m ≤ Nat.primeCounting 5 := Nat.monotone_primeCounting (by omega)
    have h5 : Nat.primeCounting 5 = 3 := by decide
    omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have := Nat.primeCounting_add_le (a := 6) (k := 6) (by norm_num) le_rfl j
    have h6 : Nat.primeCounting 6 = 3 := by decide
    have ht : Nat.totient 6 = 2 := by decide
    rw [h6, ht] at this
    omega

lemma pow_contra (n k c j N : ℕ) (hn : N ≤ n) (hN : 0 < N) (hj : j ≤ k)
    (h : n ^ k ≤ c * n ^ j) (hc : c < N ^ (k - j)) : False := by
  have hn0 : 0 < n := by omega
  have hnpos : 0 < n ^ j := by positivity
  have h1 : n ^ (k - j) * n ^ j ≤ c * n ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj]; exact h
  have h2 := Nat.le_of_mul_le_mul_right h1 hnpos
  have h3 : N ^ (k - j) ≤ n ^ (k - j) := Nat.pow_le_pow_left hn _
  omega

lemma regimeA (n k : ℕ) (hk : 0 < k) (hkk : k * k ≤ n) (h2k : 2 * k ≤ n)
    (H : ∀ p, p.Prime → p ∣ n.choose k → p ≤ k) : n ≤ 123 := by
  have hkn : k ≤ n := by omega
  have hn : 0 < n := by omega
  have hA : n ^ k ≤ k ^ k * n ^ Nat.primeCounting k :=
    (lb_A n k hkn).trans (Nat.mul_le_mul_left _ (ub_A n k hn hkn H))
  have hP := pi_bound k
  rcases Nat.lt_or_ge k 19 with hk19 | hk19
  · by_contra hbig
    push_neg at hbig
    interval_cases k <;>
      exact pow_contra n _ _ _ 124 (by omega) (by norm_num) (by decide +kernel) hA
        (by decide +kernel)
  · exfalso
    set P := Nat.primeCounting k
    have hPk : P ≤ k := by omega
    have h1 : n ^ (k - P) * n ^ P ≤ k ^ k * n ^ P := by
      rw [← pow_add, Nat.sub_add_cancel hPk]; exact hA
    have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    have h3 : (k * k) ^ (k - P) ≤ n ^ (k - P) := Nat.pow_le_pow_left hkk _
    have h4 : k ^ (2 * (k - P)) ≤ k ^ k := by
      rw [pow_mul, sq]; omega
    have h5 : k < 2 * (k - P) := by omega
    have h6 : k ^ k < k ^ (2 * (k - P)) := Nat.pow_lt_pow_right (by omega) h5
    omega


lemma lemQ (s : ℕ) (hs : 100 ≤ s) : 8 ^ s * (s + 1) ^ 20 ≤ 27 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    have h1 : (s + 2) * 101 ≤ 102 * (s + 1) := by omega
    have h2 : ((s + 2) * 101) ^ 20 ≤ (102 * (s + 1)) ^ 20 := Nat.pow_le_pow_left h1 20
    rw [mul_pow, mul_pow] at h2
    have h3 : 8 * 102 ^ 20 ≤ 27 * 101 ^ 20 := by norm_num
    have h4 : 8 * (s + 2) ^ 20 * 101 ^ 20 ≤ 27 * (s + 1) ^ 20 * 101 ^ 20 := by
      calc 8 * (s + 2) ^ 20 * 101 ^ 20 = 8 * ((s + 2) ^ 20 * 101 ^ 20) := by ring
        _ ≤ 8 * (102 ^ 20 * (s + 1) ^ 20) := Nat.mul_le_mul_left _ h2
        _ = (8 * 102 ^ 20) * (s + 1) ^ 20 := by ring
        _ ≤ (27 * 101 ^ 20) * (s + 1) ^ 20 := Nat.mul_le_mul_right _ h3
        _ = 27 * (s + 1) ^ 20 * 101 ^ 20 := by ring
    have h5 := Nat.le_of_mul_le_mul_right h4 (by norm_num)
    calc 8 ^ (s + 1) * (s + 1 + 1) ^ 20 = 8 ^ s * (8 * (s + 2) ^ 20) := by ring
      _ ≤ 8 ^ s * (27 * (s + 1) ^ 20) := Nat.mul_le_mul_left _ h5
      _ = 27 * (8 ^ s * (s + 1) ^ 20) := by ring
      _ ≤ 27 * 27 ^ s := Nat.mul_le_mul_left _ ih
      _ = 27 ^ (s + 1) := by ring

lemma lemG (s : ℕ) (hs : 100 ≤ s) : 27 * (s + 1) ^ (16 * s + 192) * 8 ^ (s * s) < 27 ^ (s * s) := by
  have hQ := lemQ s hs
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 10 := ⟨s - 10, by omega⟩
  have e1 : (t + 10 + 1) ^ (16 * (t + 10) + 192) ≤ ((t + 10 + 1) ^ 20) ^ t := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have e2 : (8 ^ (t + 10) * (t + 10 + 1) ^ 20) ^ t ≤ (27 ^ (t + 10)) ^ t := Nat.pow_le_pow_left hQ _
  have e3 : 27 * 8 ^ (t + 10) < 27 ^ (t + 10) := by
    have h27 : 27 < (t + 10 + 1) ^ 20 := by
      calc 27 < 11 ^ 20 := by norm_num
        _ ≤ (t + 10 + 1) ^ 20 := Nat.pow_le_pow_left (by omega) _
    calc 27 * 8 ^ (t + 10) < (t + 10 + 1) ^ 20 * 8 ^ (t + 10) :=
          Nat.mul_lt_mul_of_pos_right h27 (by positivity)
      _ = 8 ^ (t + 10) * (t + 10 + 1) ^ 20 := by ring
      _ ≤ _ := hQ
  have e4 : 8 ^ (9 * (t + 10)) ≤ 27 ^ (9 * (t + 10)) := Nat.pow_le_pow_left (by norm_num) _
  have e5 : 27 * 8 ^ (10 * (t + 10)) < 27 ^ (10 * (t + 10)) := by
    calc 27 * 8 ^ (10 * (t + 10)) = (27 * 8 ^ (t + 10)) * 8 ^ (9 * (t + 10)) := by ring
      _ < 27 ^ (t + 10) * 8 ^ (9 * (t + 10)) := Nat.mul_lt_mul_of_pos_right e3 (by positivity)
      _ ≤ 27 ^ (t + 10) * 27 ^ (9 * (t + 10)) := Nat.mul_le_mul_left _ e4
      _ = 27 ^ (10 * (t + 10)) := by ring
  have hss : (t + 10) * (t + 10) = (t + 10) * t + 10 * (t + 10) := by ring
  have id1 : ∀ a b A : ℕ, a * A ^ t * b ^ ((t + 10) * (t + 10)) =
      (a * b ^ (10 * (t + 10))) * (b ^ (t + 10) * A) ^ t := by
    intro a b A; rw [hss, pow_add, pow_mul, mul_pow]; ring
  have id2 : ∀ a : ℕ, a ^ (10 * (t + 10)) * (a ^ (t + 10)) ^ t = a ^ ((t + 10) * (t + 10)) := by
    intro a; rw [hss, pow_add, pow_mul]; ring
  calc 27 * (t + 10 + 1) ^ (16 * (t + 10) + 192) * 8 ^ ((t + 10) * (t + 10))
      ≤ 27 * ((t + 10 + 1) ^ 20) ^ t * 8 ^ ((t + 10) * (t + 10)) := by
        apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ e1
    _ = (27 * 8 ^ (10 * (t + 10))) * (8 ^ (t + 10) * (t + 10 + 1) ^ 20) ^ t := id1 _ _ _
    _ ≤ (27 * 8 ^ (10 * (t + 10))) * (27 ^ (t + 10)) ^ t := Nat.mul_le_mul_left _ e2
    _ < 27 ^ (10 * (t + 10)) * (27 ^ (t + 10)) ^ t :=
        Nat.mul_lt_mul_of_pos_right e5 (by positivity)
    _ = 27 ^ ((t + 10) * (t + 10)) := id2 _

lemma swap_pow (a b x y : ℕ) (hxy : x ≤ y) (hab : a ≤ b) : a ^ y * b ^ x ≤ b ^ y * a ^ x := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
  calc a ^ (x + d) * b ^ x = (a ^ x * b ^ x) * a ^ d := by ring
    _ ≤ (a ^ x * b ^ x) * b ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab d)
    _ = b ^ (x + d) * a ^ x := by ring

lemma lemEstar (n s P : ℕ) (hs : 100 ≤ s) (hsn : s * s ≤ n) (hns : n < (s + 1) * (s + 1))
    (hP : 3 * P ≤ s + 9) : 3 * 2 ^ n * n ^ (8 * P + 8) < 3 ^ n := by
  have hG := lemG s hs
  have hn1 : 1 ≤ n := by nlinarith
  have a1 : n ^ (24 * P + 24) ≤ n ^ (8 * s + 96) := Nat.pow_le_pow_right hn1 (by omega)
  have a2 : n ^ (8 * s + 96) ≤ ((s + 1) * (s + 1)) ^ (8 * s + 96) := Nat.pow_le_pow_left hns.le _
  have a3 : ((s + 1) * (s + 1)) ^ (8 * s + 96) = (s + 1) ^ (16 * s + 192) := by
    rw [← pow_two, ← pow_mul]; congr 1; ring
  have hsw : 8 ^ n * 27 ^ (s * s) ≤ 27 ^ n * 8 ^ (s * s) := swap_pow 8 27 (s * s) n hsn (by norm_num)
  have hX : (3 * 2 ^ n * n ^ (8 * P + 8)) ^ 3 = 27 * 8 ^ n * n ^ (24 * P + 24) := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
    ring_nf
  have h27 : (3 * 2 ^ n * n ^ (8 * P + 8)) ^ 3 * 27 ^ (s * s) < (3 ^ n) ^ 3 * 27 ^ (s * s) := by
    rw [hX]
    calc 27 * 8 ^ n * n ^ (24 * P + 24) * 27 ^ (s * s)
        ≤ 27 * 8 ^ n * (s + 1) ^ (16 * s + 192) * 27 ^ (s * s) := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; rw [← a3]; exact a1.trans a2
      _ = 27 * (s + 1) ^ (16 * s + 192) * (8 ^ n * 27 ^ (s * s)) := by ring
      _ ≤ 27 * (s + 1) ^ (16 * s + 192) * (27 ^ n * 8 ^ (s * s)) := Nat.mul_le_mul_left _ hsw
      _ = (27 * (s + 1) ^ (16 * s + 192) * 8 ^ (s * s)) * 27 ^ n := by ring
      _ < 27 ^ (s * s) * 27 ^ n := Nat.mul_lt_mul_of_pos_right hG (by positivity)
      _ = (3 ^ n) ^ 3 * 27 ^ (s * s) := by
          have e : ((3 : ℕ) ^ n) ^ 3 = 27 ^ n := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [e, mul_comm]
  have h3 := Nat.lt_of_mul_lt_mul_right h27
  exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h3

lemma lemE1 (n s P : ℕ) (hs : 100 ≤ s) (hsn : s * s ≤ n) (hP : 3 * P ≤ s + 9)
    (h : n ^ (s + 1) ≤ n ^ P * (2 * s + 2) ^ (s + 2)) : False := by
  have hn1 : 1 ≤ n := by nlinarith
  have h3 : (n ^ (s + 1)) ^ 3 ≤ (n ^ P * (2 * s + 2) ^ (s + 2)) ^ 3 := Nat.pow_le_pow_left h 3
  rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at h3
  have h4 : n ^ (P * 3) ≤ n ^ (s + 9) := Nat.pow_le_pow_right hn1 (by omega)
  have h5 : n ^ (s + 9) * n ^ (2 * s - 6) ≤ n ^ (s + 9) * (2 * s + 2) ^ ((s + 2) * 3) := by
    rw [← pow_add, show s + 9 + (2 * s - 6) = (s + 1) * 3 by omega]
    exact h3.trans (Nat.mul_le_mul_right _ h4)
  have h6 := Nat.le_of_mul_le_mul_left h5 (by positivity)
  have h7 : (s * s) ^ (2 * s - 6) ≤ n ^ (2 * s - 6) := Nat.pow_le_pow_left hsn _
  have b1 : 100 * (2 * s + 2) ≤ 202 * s := by omega
  have b2 : (100 * (2 * s + 2)) ^ 5 ≤ (202 * s) ^ 5 := Nat.pow_le_pow_left b1 5
  rw [mul_pow, mul_pow] at b2
  have b3 : 202 ^ 5 * s ^ 5 ≤ 100 ^ 5 * s ^ 6 := by
    have : 202 ^ 5 ≤ 100 ^ 5 * s := by nlinarith
    calc 202 ^ 5 * s ^ 5 ≤ (100 ^ 5 * s) * s ^ 5 := Nat.mul_le_mul_right _ this
      _ = 100 ^ 5 * s ^ 6 := by ring
  have b4 : (2 * s + 2) ^ 5 ≤ s ^ 6 :=
    Nat.le_of_mul_le_mul_left (b2.trans b3) (by norm_num)
  have c1 : ((2 * s + 2) ^ ((s + 2) * 3)) ^ 5 < ((s * s) ^ (2 * s - 6)) ^ 5 := by
    calc ((2 * s + 2) ^ ((s + 2) * 3)) ^ 5 = ((2 * s + 2) ^ 5) ^ ((s + 2) * 3) := by
          rw [← pow_mul, ← pow_mul]; congr 1; ring
      _ ≤ (s ^ 6) ^ ((s + 2) * 3) := Nat.pow_le_pow_left b4 _
      _ = s ^ (18 * s + 36) := by rw [← pow_mul]; ring_nf
      _ < s ^ (20 * s - 60) := Nat.pow_lt_pow_right (by omega) (by omega)
      _ = ((s * s) ^ (2 * s - 6)) ^ 5 := by
          rw [← pow_two, ← pow_mul, ← pow_mul]; congr 1; omega
  have c2 := (Nat.pow_lt_pow_iff_left (by norm_num)).1 c1
  omega

lemma mono_step (n j : ℕ) (hj : 1 ≤ j) (h8 : 8 * (j + 1) ≤ n) :
    n ^ j * (2 * j + 2) ^ (j + 2) ≤ n ^ (j + 1) * (2 * j) ^ (j + 1) := by
  have K := keyK j hj
  calc n ^ j * (2 * j + 2) ^ (j + 2) = n ^ j * 2 ^ (j + 2) * (j + 1) * (j + 1) ^ (j + 1) := by
        rw [show 2 * j + 2 = 2 * (j + 1) by ring, mul_pow]; ring
    _ ≤ n ^ j * 2 ^ (j + 2) * (j + 1) * (4 * j ^ (j + 1)) := Nat.mul_le_mul_left _ K
    _ = (8 * (j + 1)) * (n ^ j * 2 ^ (j + 1) * j ^ (j + 1)) := by ring
    _ ≤ n * (n ^ j * 2 ^ (j + 1) * j ^ (j + 1)) := Nat.mul_le_mul_right _ h8
    _ = n ^ (j + 1) * (2 * j) ^ (j + 1) := by rw [mul_pow]; ring

lemma mono_chain (n s : ℕ) (hs1 : 1 ≤ s) : ∀ k, s + 1 ≤ k → 8 * k ≤ n →
    n ^ (s + 1) * (2 * k) ^ (k + 1) ≤ n ^ k * (2 * s + 2) ^ (s + 2) := by
  intro k hsk
  induction k, hsk using Nat.le_induction with
  | base => intro _; exact le_of_eq (by ring)
  | succ k hk ih =>
    intro h8
    have ih' := ih (by omega)
    have M := mono_step n k (by omega) h8
    have hn0 : 0 < n := by omega
    have hpos : 0 < n ^ k := by positivity
    have : n ^ (s + 1) * (2 * (k + 1)) ^ (k + 1 + 1) * n ^ k ≤
        n ^ (k + 1) * (2 * s + 2) ^ (s + 2) * n ^ k := by
      calc n ^ (s + 1) * (2 * (k + 1)) ^ (k + 1 + 1) * n ^ k
          = n ^ (s + 1) * (n ^ k * (2 * k + 2) ^ (k + 2)) := by ring
        _ ≤ n ^ (s + 1) * (n ^ (k + 1) * (2 * k) ^ (k + 1)) := Nat.mul_le_mul_left _ M
        _ = n ^ (k + 1) * (n ^ (s + 1) * (2 * k) ^ (k + 1)) := by ring
        _ ≤ n ^ (k + 1) * (n ^ k * (2 * s + 2) ^ (s + 2)) := Nat.mul_le_mul_left _ ih'
        _ = n ^ (k + 1) * (2 * s + 2) ^ (s + 2) * n ^ k := by ring
    exact Nat.le_of_mul_le_mul_right this hpos


lemma large_case (n k : ℕ) (hk : 0 < k) (h2k : 2 * k ≤ n) (hsk : Nat.sqrt n < k)
    (hbig : 10001 ≤ n) (H : ∀ p, p.Prime → p ∣ n.choose k → p ≤ k) : False := by
  have hkn : k ≤ n := by omega
  have hn : 0 < n := by omega
  set s := Nat.sqrt n with hsdef
  have hs100 : 100 ≤ s := Nat.le_sqrt.2 (by omega)
  have hsn : s * s ≤ n := Nat.sqrt_le n
  have hns : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  set P := Nat.primeCounting s with hPdef
  have hP : 3 * P ≤ s + 9 := pi_bound s
  have hE := lemEstar n s P hs100 hsn hns hP
  by_cases h3 : 3 * k ≤ n
  · have hub := ub_B n k k hn hkn H
    have hlb := lb_B n k hk h2k
    have hmain : n ^ k ≤ (2 * k) ^ (k + 1) * n ^ P := by
      have : n ^ k * 4 ^ k ≤ ((2 * k) ^ (k + 1) * n ^ P) * 4 ^ k := by
        calc n ^ k * 4 ^ k = 4 ^ k * n ^ k := by ring
          _ ≤ (2 * k) ^ (k + 1) * n.choose k := hlb
          _ ≤ (2 * k) ^ (k + 1) * (n ^ P * 4 ^ k) := Nat.mul_le_mul_left _ hub
          _ = ((2 * k) ^ (k + 1) * n ^ P) * 4 ^ k := by ring
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    by_cases h8 : 8 * k ≤ n
    · have hc := mono_chain n s (by omega) k (by omega) h8
      have : n ^ (s + 1) * (2 * k) ^ (k + 1) ≤ (n ^ P * (2 * s + 2) ^ (s + 2)) * (2 * k) ^ (k + 1) := by
        calc n ^ (s + 1) * (2 * k) ^ (k + 1) ≤ n ^ k * (2 * s + 2) ^ (s + 2) := hc
          _ ≤ ((2 * k) ^ (k + 1) * n ^ P) * (2 * s + 2) ^ (s + 2) := Nat.mul_le_mul_right _ hmain
          _ = (n ^ P * (2 * s + 2) ^ (s + 2)) * (2 * k) ^ (k + 1) := by ring
      exact lemE1 n s P hs100 hsn hP (Nat.le_of_mul_le_mul_right this (by positivity))
    · push_neg at h8
      -- 3^(k+1) ≤ 2^(k+1) * n^(P+1)
      have hA : 3 ^ (k + 1) * (2 * k) ^ (k + 1) ≤ 2 ^ (k + 1) * n ^ (k + 1) := by
        rw [← mul_pow, ← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
      have hB : 3 ^ (k + 1) * n ^ k ≤ (2 ^ (k + 1) * n ^ (P + 1)) * n ^ k := by
        calc 3 ^ (k + 1) * n ^ k ≤ 3 ^ (k + 1) * ((2 * k) ^ (k + 1) * n ^ P) :=
              Nat.mul_le_mul_left _ hmain
          _ = (3 ^ (k + 1) * (2 * k) ^ (k + 1)) * n ^ P := by ring
          _ ≤ (2 ^ (k + 1) * n ^ (k + 1)) * n ^ P := Nat.mul_le_mul_right _ hA
          _ = (2 ^ (k + 1) * n ^ (P + 1)) * n ^ k := by ring
      have hC := Nat.le_of_mul_le_mul_right hB (by positivity)
      have hD : (3 ^ (k + 1)) ^ 8 ≤ (2 ^ (k + 1) * n ^ (P + 1)) ^ 8 := Nat.pow_le_pow_left hC 8
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at hD
      have hsw := swap_pow 2 3 n ((k + 1) * 8) (by omega) (by norm_num)
      have hF : 3 ^ n * 2 ^ ((k + 1) * 8) ≤ (2 ^ n * n ^ ((P + 1) * 8)) * 2 ^ ((k + 1) * 8) := by
        calc 3 ^ n * 2 ^ ((k + 1) * 8) = 2 ^ ((k + 1) * 8) * 3 ^ n := by ring
          _ ≤ 3 ^ ((k + 1) * 8) * 2 ^ n := hsw
          _ ≤ (2 ^ ((k + 1) * 8) * n ^ ((P + 1) * 8)) * 2 ^ n := Nat.mul_le_mul_right _ hD
          _ = (2 ^ n * n ^ ((P + 1) * 8)) * 2 ^ ((k + 1) * 8) := by ring
      have hG := Nat.le_of_mul_le_mul_right hF (by positivity)
      rw [show (P + 1) * 8 = 8 * P + 8 by ring] at hG
      rw [show 3 * 2 ^ n * n ^ (8 * P + 8) = 3 * (2 ^ n * n ^ (8 * P + 8)) by ring] at hE
      omega
  · push_neg at h3
    set m := n / 3 with hm
    have hm1 : 3333 ≤ m := by omega
    have H' : ∀ p, p.Prime → p ∣ n.choose k → p ≤ m := by
      intro p hp hd
      by_contra hlt
      push_neg at hlt
      have hpk := H p hp hd
      have hz := Nat.factorization_choose_of_lt_three_mul (n := n) (k := k) (p := p)
        (by omega) hpk (by omega) (by omega)
      have hpos := hp.factorization_pos_of_dvd (Nat.choose_pos hkn).ne' hd
      omega
    have hub := ub_B n k m hn hkn H'
    have hlb := lb_C n k m (by omega) (by omega) h2k (by omega)
    -- 6^m ≤ 2m * n^P * 4^m  ⇒  3^m ≤ 2m * 2^m * n^P
    have h1 : 3 ^ m * 2 ^ m ≤ (2 * m * 2 ^ m * n ^ P) * 2 ^ m := by
      calc 3 ^ m * 2 ^ m = 6 ^ m := by rw [← mul_pow]; norm_num
        _ ≤ 2 * m * n.choose k := hlb
        _ ≤ 2 * m * (n ^ P * 4 ^ m) := Nat.mul_le_mul_left _ hub
        _ = (2 * m * 2 ^ m * n ^ P) * 2 ^ m := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
    have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    have h3' : (3 ^ m) ^ 3 ≤ (2 * m * 2 ^ m * n ^ P) ^ 3 := Nat.pow_le_pow_left h2 3
    have h4 : (2 * m) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h5 : 3 ^ n ≤ 9 * (3 ^ m) ^ 3 := by
      rw [← pow_mul]
      calc 3 ^ n ≤ 3 ^ (m * 3 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 * 3 ^ (m * 3) := by ring
    have h6 : (2 ^ m) ^ 3 ≤ 2 ^ n := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h7 : 3 ^ n ≤ 9 * (n ^ (3 * P + 3) * 2 ^ n) := by
      calc 3 ^ n ≤ 9 * (3 ^ m) ^ 3 := h5
        _ ≤ 9 * (2 * m * 2 ^ m * n ^ P) ^ 3 := Nat.mul_le_mul_left _ h3'
        _ = 9 * ((2 * m) ^ 3 * (2 ^ m) ^ 3 * n ^ (3 * P)) := by
            rw [mul_pow, mul_pow, ← pow_mul]; ring
        _ ≤ 9 * (n ^ 3 * 2 ^ n * n ^ (3 * P)) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h4 h6)
        _ = 9 * (n ^ (3 * P + 3) * 2 ^ n) := by ring
    have h8 : 3 * n ^ (3 * P + 3) ≤ n ^ (8 * P + 8) := by
      calc 3 * n ^ (3 * P + 3) ≤ n ^ (5 * P + 5) * n ^ (3 * P + 3) := by
            apply Nat.mul_le_mul_right
            calc 3 ≤ n := by omega
              _ = n ^ 1 := (pow_one n).symm
              _ ≤ n ^ (5 * P + 5) := Nat.pow_le_pow_right hn (by omega)
        _ = n ^ (8 * P + 8) := by rw [← pow_add]; ring_nf
    have h9 : 9 * (n ^ (3 * P + 3) * 2 ^ n) ≤ 3 * 2 ^ n * n ^ (8 * P + 8) := by
      calc 9 * (n ^ (3 * P + 3) * 2 ^ n) = 3 * 2 ^ n * (3 * n ^ (3 * P + 3)) := by ring
        _ ≤ 3 * 2 ^ n * n ^ (8 * P + 8) := Nat.mul_le_mul_left _ h8
    omega


def Good (n : ℕ) : Prop := ∃ q, q.Prime ∧ q ≤ n ∧ n ≤ q + Nat.sqrt n

theorem chain_step {a N : ℕ} (q M r : ℕ) (hq : q.Prime) (hqM : q ≤ M) (hr : r * r ≤ M)
    (hN : N ≤ q + r + 1) (H : ∀ n, a ≤ n → n < M → Good n) :
    ∀ n, a ≤ n → n < N → Good n := by
  intro n han hnN
  by_cases hnM : n < M
  · exact H n han hnM
  · refine ⟨q, hq, by omega, ?_⟩
    have : r ≤ Nat.sqrt n := Nat.le_sqrt.2 (by nlinarith)
    omega

theorem chain_low : ∀ n, 5 ≤ n → n < 125 → Good n := by
  refine chain_step 113 121 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 113 113 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 103 103 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 97 97 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 89 89 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 79 81 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 73 73 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 67 67 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 59 59 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 53 53 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 47 47 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 41 41 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 37 37 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 31 31 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 29 29 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 23 25 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 23 23 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 19 19 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 17 17 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 13 13 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 11 11 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7 9 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7 7 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro n h1 h2
  omega

theorem chain_high : ∀ n, 127 ≤ n → n < 10001 → Good n := by
  refine chain_step 9901 9901 99 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9803 9803 97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9719 9719 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9623 9623 95 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9533 9533 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9437 9437 95 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9341 9341 95 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9257 9257 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9161 9161 95 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 9067 9067 93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8999 8999 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8923 8923 75 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8831 8831 91 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8737 8737 93 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8647 8647 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8563 8563 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8501 8501 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8419 8419 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8329 8329 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8243 8243 85 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8161 8161 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 8081 8081 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7993 7993 87 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7907 7907 85 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7823 7823 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7741 7741 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7669 7669 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7583 7583 85 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7499 7499 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7417 7417 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7331 7331 85 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7247 7247 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7177 7177 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7103 7103 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 7019 7019 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6947 6947 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6869 6869 77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6791 6791 77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6709 6709 81 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6637 6637 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6563 6563 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6491 6491 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6421 6421 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6343 6343 77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6263 6263 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6197 6197 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6121 6121 75 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 6043 6043 77 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5981 5981 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5923 5923 57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5849 5849 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5779 5779 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5711 5711 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5639 5639 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5569 5569 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5501 5501 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5431 5431 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5381 5381 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5309 5309 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5237 5237 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5167 5167 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5099 5099 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 5039 5039 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4969 4969 69 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4903 4903 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4861 4861 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4793 4793 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4729 4729 63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4663 4663 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4597 4597 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4547 4547 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4481 4481 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4421 4421 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4357 4357 63 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4297 4297 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4231 4231 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4177 4177 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4127 4127 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4073 4073 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 4013 4013 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3967 3967 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3907 3907 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3847 3847 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3793 3793 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3733 3733 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3673 3673 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3613 3613 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3557 3557 55 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3499 3499 57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3449 3449 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3391 3391 57 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3343 3343 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3299 3299 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3251 3251 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3203 3203 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3163 3163 39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3109 3109 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3061 3061 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 3011 3011 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2957 2957 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2903 2903 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2851 2851 51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2801 2801 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2749 2749 51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2699 2699 49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2647 2647 51 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2609 2609 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2579 2579 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2531 2531 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2503 2503 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2459 2459 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2411 2411 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2371 2371 39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2333 2333 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2287 2287 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2239 2239 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2203 2203 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2161 2161 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2129 2129 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2083 2083 45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 2039 2039 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1997 1997 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1973 1973 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1931 1931 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1889 1889 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1847 1847 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1811 1811 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1777 1777 33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1741 1741 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1699 1699 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1663 1663 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1627 1627 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1597 1597 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1559 1559 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1523 1523 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1487 1487 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1451 1451 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1423 1423 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1399 1399 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1367 1367 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1361 1361 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1327 1327 33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1291 1291 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1259 1259 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1223 1225 35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1193 1193 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1163 1163 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1129 1129 33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1097 1097 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1069 1069 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1039 1039 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 1009 1009 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 977 977 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 947 947 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 919 919 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 907 907 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 877 877 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 853 853 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 827 827 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 809 809 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 787 787 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 761 761 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 733 733 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 709 709 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 683 683 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 659 659 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 641 641 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 617 617 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 593 593 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 569 569 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 547 547 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 523 529 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 509 509 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 487 487 21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 467 467 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 449 449 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 431 431 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 419 419 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 401 401 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 383 383 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 367 367 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 349 349 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 331 331 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 313 313 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 307 307 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 293 293 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 277 277 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 263 263 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 251 251 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 239 239 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 223 225 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 211 211 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 197 197 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 191 191 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 179 179 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 167 167 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 157 157 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 149 149 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 137 137 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  refine chain_step 127 127 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_
  intro n h1 h2
  omega

set_option maxRecDepth 100000 in
theorem dcheck1 : ∀ n < 124, ∀ k < 12, (1 ≤ k ∧ 2 * k ≤ n ∧ k * k ≤ n) →
    ∃ i < k, ¬ (n - i) ∣ (k.factorial) ^ (n - i) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dcheck2 : ∀ n < 127, ∀ k < 64, (125 ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n) →
    ∃ i < k, ¬ (n - i) ∣ (k.factorial) ^ (n - i) := by
  decide +kernel

theorem main_thm (n k : ℕ) (hk : 0 < k) (h2k : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ k < p ∧ p ∣ n.choose k := by
  by_contra hcon
  push_neg at hcon
  have H : ∀ p, p.Prime → p ∣ n.choose k → p ≤ k := fun p hp hd => by
    by_contra h
    push_neg at h
    exact hcon p hp h hd
  have hkn : k ≤ n := by omega
  by_cases hA : k * k ≤ n
  · have h1 := regimeA n k hk hA h2k H
    have hk12 : k < 12 := by
      by_contra h; push_neg at h; nlinarith
    obtain ⟨p, hp, hkp, hd⟩ := direct_ok hkn (dcheck1 n (by omega) k hk12 ⟨hk, h2k, hA⟩)
    exact hcon p hp hkp hd
  · push_neg at hA
    have hsk : Nat.sqrt n < k := Nat.sqrt_lt.2 hA
    by_cases hsmall : n < 10001
    · by_cases h125 : 125 ≤ n ∧ n < 127
      · obtain ⟨p, hp, hkp, hd⟩ := direct_ok hkn (dcheck2 n h125.2 k (by omega) ⟨h125.1, hk, h2k⟩)
        exact hcon p hp hkp hd
      · have hk3 : 3 ≤ k := by
          by_contra h; push_neg at h
          interval_cases k <;> omega
        have hG : Good n := by
          by_cases hlow : n < 125
          · exact chain_low n (by omega) hlow
          · exact chain_high n (by omega) hsmall
        obtain ⟨q, hq, hqn, hnq⟩ := hG
        have hqk : k < q := by omega
        have hd : q ∣ n.choose k :=
          dvd_choose_of_block hq (i := n - q) (by omega) hkn hqk
            (by rw [show n - (n - q) = q by omega])
        exact hcon q hq hqk hd
    · push_neg at hsmall
      exact large_case n k hk h2k hsk hsmall H

end SylvSchur

theorem OMA.solution : type_of% @Erdos683.erdos_683.variant.sylvester_schur := by
  intro n k ⟨hk, hkn⟩
  have h2k : 2 * k ≤ n := by omega
  obtain ⟨p, hp, hkp, hd⟩ := SylvSchur.main_thm n k hk h2k
  exact SylvSchur.P_gt_of_dvd hp hkp hd (by omega)
