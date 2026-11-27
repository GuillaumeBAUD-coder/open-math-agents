import OMAStatements.S_oeis_a361034

/-!
Proof of OEIS A361034: for a(n) = 2520 * (4n)! / (n! * (n+2)!^3),
we show n! * (n+2)!^3 divides 2520 * (4n)! via prime factorizations
and obtain v_2(a(n)) = 3 * (s_2(n+2) - 1), so a(n) is odd iff n + 2 = 2^k with k ≥ 1.
-/

private lemma sum_digits_two_pos {m : ℕ} (hm : m ≠ 0) : 1 ≤ (Nat.digits 2 m).sum := by
  have hnil : Nat.digits 2 m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hm)⟩

private lemma sum_digits_two_two_mul (m : ℕ) :
    (Nat.digits 2 (2 * m)).sum = (Nat.digits 2 m).sum := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [← zero_add (2 * m), Nat.digits_add 2 one_lt_two 0 m (by norm_num) (Or.inr hm)]
    simp

private lemma sum_digits_two_eq_one_iff (m : ℕ) :
    (Nat.digits 2 m).sum = 1 ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · intro h
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases eq_or_ne m 0 with rfl | hm
      · simp at h
      have hdig : Nat.digits 2 m = (m % 2) :: Nat.digits 2 (m / 2) :=
        Nat.digits_eq_cons_digits_div one_lt_two hm
      rw [hdig, List.sum_cons] at h
      rcases Nat.mod_two_eq_zero_or_one m with hmod | hmod
      · rw [hmod, zero_add] at h
        obtain ⟨k, hk⟩ := ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) one_lt_two) h
        exact ⟨k + 1, by omega⟩
      · rw [hmod] at h
        have hm2 : m / 2 = 0 := by
          by_contra hne
          have h1 := sum_digits_two_pos hne
          omega
        exact ⟨0, by omega⟩
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', sum_digits_two_two_mul, ih]

private lemma term_le_of_four_le {M n : ℕ} (c : ℕ) (hM : 4 ≤ M) (hc : 8 ≤ M + 4 * c) :
    n / M + 3 * ((n + 2) / M) ≤ (4 * n) / M + c := by
  have hMpos : 0 < M := by omega
  set q := n / M
  set r := n % M
  have hnr : M * q + r = n := Nat.div_add_mod n M
  have hr : r < M := Nat.mod_lt n hMpos
  by_cases hr2 : r + 2 < M
  · have hq2 : (n + 2) / M = q := by
      rw [← hnr, add_assoc, Nat.mul_add_div hMpos, Nat.div_eq_of_lt hr2, add_zero]
    have h4q : 4 * q ≤ (4 * n) / M := by
      rw [Nat.le_div_iff_mul_le hMpos]
      nlinarith
    omega
  · have hq2 : (n + 2) / M = q + 1 := by
      have hr' : r + 2 - M < M := by omega
      have hn2 : M * (q + 1) + (r + 2 - M) = n + 2 := by
        rw [mul_add, mul_one]
        omega
      rw [← hn2, Nat.mul_add_div hMpos, Nat.div_eq_of_lt hr', add_zero]
    rcases le_or_gt 3 c with hc3 | hc3
    · have h4q : 4 * q ≤ (4 * n) / M := by
        rw [Nat.le_div_iff_mul_le hMpos]
        nlinarith
      omega
    · have hmul : (4 * q + 3 - c) * M ≤ 4 * n := by
        have h1 : (4 * q + 3 - c) * M + c * M = (4 * q + 3) * M := by
          rw [← add_mul]
          congr 1
          omega
        nlinarith
      have hdiv : 4 * q + 3 - c ≤ (4 * n) / M := (Nat.le_div_iff_mul_le hMpos).mpr hmul
      omega

private lemma odd_prime_factorization_le
    {n p : ℕ} (c : ℕ) (hn0 : n ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hterm1 : n / p + 3 * ((n + 2) / p) ≤ (4 * n) / p + c)
    (hc : p ^ c ∣ 2520) :
    (n.factorial * (n + 2).factorial ^ 3).factorization p ≤
      (2520 * (4 * n).factorial).factorization p := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  let b := 4 * n + 1
  have hlog4 : Nat.log p (4 * n) < b :=
    Nat.lt_succ_of_le (Nat.log_le_self p (4 * n))
  have hlog0 : Nat.log p n < b :=
    Nat.lt_succ_of_le ((Nat.log_le_self p n).trans (by omega))
  have hlog2 : Nat.log p (n + 2) < b :=
    Nat.lt_succ_of_le ((Nat.log_le_self p (n + 2)).trans (by omega))
  have hDf : (n.factorial * (n + 2).factorial ^ 3).factorization p =
      ∑ i ∈ Finset.Ico 1 b, (n / p ^ i + 3 * ((n + 2) / p ^ i)) := by
    rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
      Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Nat.factorization_factorial hp hlog0, Nat.factorization_factorial hp hlog2,
      Finset.mul_sum, ← Finset.sum_add_distrib]
  have h4f : (4 * n).factorial.factorization p =
      ∑ i ∈ Finset.Ico 1 b, (4 * n) / p ^ i :=
    Nat.factorization_factorial hp hlog4
  have hc_le : c ≤ (2520 : ℕ).factorization p := by
    have hdvd := (Nat.factorization_le_iff_dvd (pow_ne_zero c hp.ne_zero) (by decide)).mpr hc p
    rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      hp.factorization_self, mul_one] at hdvd
    exact hdvd
  have hNf : (4 * n).factorial.factorization p + c ≤ (2520 * (4 * n).factorial).factorization p := by
    rw [Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _), Finsupp.coe_add, Pi.add_apply]
    omega
  refine le_trans ?_ hNf
  rw [hDf, h4f]
  have h1mem : (1 : ℕ) ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  calc
    ∑ i ∈ Finset.Ico 1 b, (n / p ^ i + 3 * ((n + 2) / p ^ i))
        ≤ ∑ i ∈ Finset.Ico 1 b, ((4 * n) / p ^ i + if i = 1 then c else 0) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
      split_ifs with hi_eq
      · subst hi_eq
        simpa only [pow_one] using hterm1
      · rw [add_zero]
        have hi2 : 2 ≤ i := by omega
        have hpow : 8 ≤ p ^ i := by
          calc 8 ≤ 3 ^ 2 := by norm_num
            _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
            _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi2
        simpa using term_le_of_four_le (n := n) 0 (by omega) (by omega)
    _ = (∑ i ∈ Finset.Ico 1 b, (4 * n) / p ^ i) + c := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [h1mem]

theorem OMA.solution : type_of% @OMA.S_oeis_a361034.main := by
  intro n
  let N := 2520 * (4 * n).factorial
  let D := n.factorial * (n + 2).factorial ^ 3
  have hN0 : N ≠ 0 := by positivity
  have hD0 : D ≠ 0 := by positivity
  have hfac2N : N.factorization 2 = 3 + (4 * n - (Nat.digits 2 n).sum) := by
    have h2520 : (2520 : ℕ).factorization 2 = 3 := by
      have hmul2 : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
      rw [hmul2, Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow,
        Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd (by decide),
        mul_one, add_zero]
    have h4 : (4 * n).factorial.factorization 2 = 4 * n - (Nat.digits 2 (4 * n)).sum := by
      simpa using Nat.sub_one_mul_factorization_factorial (n := 4 * n) Nat.prime_two
    have hdig : (Nat.digits 2 (4 * n)).sum = (Nat.digits 2 n).sum := by
      have h4n : 4 * n = 2 * (2 * n) := by ring
      rw [h4n, sum_digits_two_two_mul, sum_digits_two_two_mul]
    rw [show N = 2520 * (4 * n).factorial from rfl,
      Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _),
      Finsupp.coe_add, Pi.add_apply, h2520, h4, hdig]
  have hfac2D : D.factorization 2 =
      (n - (Nat.digits 2 n).sum) + 3 * (n + 2 - (Nat.digits 2 (n + 2)).sum) := by
    have hn : n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := by
      simpa using Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
    have hn2 : (n + 2).factorial.factorization 2 = n + 2 - (Nat.digits 2 (n + 2)).sum := by
      simpa using Nat.sub_one_mul_factorization_factorial (n := n + 2) Nat.prime_two
    rw [show D = n.factorial * (n + 2).factorial ^ 3 from rfl,
      Nat.factorization_mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
      Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hn, hn2]
  have hs0 : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hs2 : (Nat.digits 2 (n + 2)).sum ≤ n + 2 := Nat.digit_sum_le 2 (n + 2)
  have hs2pos : 1 ≤ (Nat.digits 2 (n + 2)).sum := sum_digits_two_pos (by omega)
  have hfac2_eq : N.factorization 2 = D.factorization 2 + 3 * ((Nat.digits 2 (n + 2)).sum - 1) := by
    omega
  have hdvd : D ∣ N := by
    rcases eq_or_ne n 0 with rfl | hn0
    · dsimp [D, N]
      decide
    rw [← Nat.factorization_le_iff_dvd hD0 hN0]
    intro p
    by_cases hp : p.Prime
    · rcases eq_or_ne p 2 with rfl | hp2
      · omega
      · by_cases hp8 : 8 ≤ p
        · exact odd_prime_factorization_le 0 hn0 hp hp2
            (by simpa using term_le_of_four_le (M := p) (n := n) 0 (by omega) (by omega)) (by simp)
        · have hp_cases : p = 3 ∨ p = 5 ∨ p = 7 := by
            have := hp.two_le
            interval_cases p <;> simp_all <;> norm_num at hp
          rcases hp_cases with rfl | rfl | rfl
          · exact odd_prime_factorization_le 2 hn0 hp hp2 (by omega) (by decide)
          · exact odd_prime_factorization_le 1 hn0 hp hp2
              (term_le_of_four_le (M := 5) (n := n) 1 (by omega) (by omega)) (by decide)
          · exact odd_prime_factorization_le 1 hn0 hp hp2
              (term_le_of_four_le (M := 7) (n := n) 1 (by omega) (by omega)) (by decide)
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hmul : D * OMA.S_oeis_a361034.a n = N := by
    dsimp [OMA.S_oeis_a361034.a]
    exact Nat.mul_div_cancel' hdvd
  have ha0 : OMA.S_oeis_a361034.a n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact hN0 hmul.symm
  have ha_fac2 : (OMA.S_oeis_a361034.a n).factorization 2 =
      3 * ((Nat.digits 2 (n + 2)).sum - 1) := by
    have hmul_fac := congrArg (fun x => x.factorization 2) hmul
    rw [Nat.factorization_mul hD0 ha0, Finsupp.coe_add, Pi.add_apply] at hmul_fac
    omega
  have hodd_iff : Odd (OMA.S_oeis_a361034.a n) ↔ (OMA.S_oeis_a361034.a n).factorization 2 = 0 := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, Nat.factorization_eq_zero_iff _ 2]
    simp [Nat.prime_two, ha0]
  rw [hodd_iff, ha_fac2]
  have h3_iff : 3 * ((Nat.digits 2 (n + 2)).sum - 1) = 0 ↔ (Nat.digits 2 (n + 2)).sum = 1 := by
    omega
  rw [h3_iff, sum_digits_two_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    rcases eq_or_ne k 0 with rfl | hk0
    · simp at hk
    · exact ⟨k, by omega, by omega⟩
  · rintro ⟨k, hk1, rfl⟩
    have hpow : 2 ≤ 2 ^ k := by
      simpa using Nat.pow_le_pow_right (by norm_num) hk1
    exact ⟨k, by omega⟩
