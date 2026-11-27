import OMAStatements.S_oeis_a361033

/-!
Proof of OEIS A361033: for a(n) = 3 * (4n)! / (n! * (n+1)!^3),
we show n! * (n+1)!^3 divides 3 * (4n)! via prime factorizations
and obtain v_2(a(n)) = 3 * (s_2(n+1) - 1), so a(n) is odd iff n + 1 is a power of 2.
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

private lemma term_le_of_four_le {M n : ℕ} (hM : 4 ≤ M) :
    n / M + 3 * ((n + 1) / M) ≤ (4 * n) / M := by
  have hMpos : 0 < M := by omega
  rw [Nat.le_div_iff_mul_le hMpos]
  set q := n / M
  set r := n % M
  have hnr : M * q + r = n := Nat.div_add_mod n M
  have hr : r < M := Nat.mod_lt n hMpos
  by_cases hr1 : r + 1 < M
  · have hq1 : (n + 1) / M = q := by
      rw [← hnr, add_assoc, Nat.mul_add_div hMpos, Nat.div_eq_of_lt hr1, add_zero]
    rw [hq1]
    nlinarith
  · have hr1' : r + 1 = M := by omega
    have hq1 : (n + 1) / M = q + 1 := by
      have hn1 : n + 1 = M * (q + 1) := by linarith
      rw [hn1, Nat.mul_div_right _ hMpos]
    rw [hq1]
    nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a361033.main := by
  intro n
  let N := 3 * (4 * n).factorial
  let D := n.factorial * (n + 1).factorial ^ 3
  have hN0 : N ≠ 0 := by positivity
  have hD0 : D ≠ 0 := by positivity
  have hfac2N : N.factorization 2 = 4 * n - (Nat.digits 2 n).sum := by
    have h3 : (3 : ℕ).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by decide)
    have h4 : (4 * n).factorial.factorization 2 = 4 * n - (Nat.digits 2 (4 * n)).sum := by
      simpa using Nat.sub_one_mul_factorization_factorial (n := 4 * n) Nat.prime_two
    have hdig : (Nat.digits 2 (4 * n)).sum = (Nat.digits 2 n).sum := by
      have h4n : 4 * n = 2 * (2 * n) := by ring
      rw [h4n, sum_digits_two_two_mul, sum_digits_two_two_mul]
    rw [show N = 3 * (4 * n).factorial from rfl,
      Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _),
      Finsupp.coe_add, Pi.add_apply, h3, zero_add, h4, hdig]
  have hfac2D : D.factorization 2 =
      (n - (Nat.digits 2 n).sum) + 3 * (n + 1 - (Nat.digits 2 (n + 1)).sum) := by
    have hn : n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := by
      simpa using Nat.sub_one_mul_factorization_factorial (n := n) Nat.prime_two
    have hn1 : (n + 1).factorial.factorization 2 = n + 1 - (Nat.digits 2 (n + 1)).sum := by
      simpa using Nat.sub_one_mul_factorization_factorial (n := n + 1) Nat.prime_two
    rw [show D = n.factorial * (n + 1).factorial ^ 3 from rfl,
      Nat.factorization_mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
      Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hn, hn1]
  have hs0 : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  have hs1 : (Nat.digits 2 (n + 1)).sum ≤ n + 1 := Nat.digit_sum_le 2 (n + 1)
  have hs1pos : 1 ≤ (Nat.digits 2 (n + 1)).sum := sum_digits_two_pos (Nat.succ_ne_zero n)
  have hfac2_eq : N.factorization 2 = D.factorization 2 + 3 * ((Nat.digits 2 (n + 1)).sum - 1) := by
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
      · let b := 4 * n + 1
        have hlog4 : Nat.log p (4 * n) < b :=
          Nat.lt_succ_of_le (Nat.log_le_self p (4 * n))
        have hlog0 : Nat.log p n < b :=
          Nat.lt_succ_of_le ((Nat.log_le_self p n).trans (by omega))
        have hlog1 : Nat.log p (n + 1) < b :=
          Nat.lt_succ_of_le ((Nat.log_le_self p (n + 1)).trans (by omega))
        have hDf : D.factorization p =
            ∑ i ∈ Finset.Ico 1 b, (n / p ^ i + 3 * ((n + 1) / p ^ i)) := by
          rw [show D = n.factorial * (n + 1).factorial ^ 3 from rfl,
            Nat.factorization_mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
            Nat.factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, Nat.factorization_factorial hp hlog0, Nat.factorization_factorial hp hlog1,
            Finset.mul_sum, ← Finset.sum_add_distrib]
        have h4f : (4 * n).factorial.factorization p =
            ∑ i ∈ Finset.Ico 1 b, (4 * n) / p ^ i :=
          Nat.factorization_factorial hp hlog4
        rcases eq_or_ne p 3 with rfl | hp3
        · have hNf : N.factorization 3 = (4 * n).factorial.factorization 3 + 1 := by
            rw [show N = 3 * (4 * n).factorial from rfl,
              Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _),
              Finsupp.coe_add, Pi.add_apply, Nat.prime_three.factorization_self, add_comm]
          rw [hDf, hNf, h4f]
          have h1mem : (1 : ℕ) ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
          calc
            ∑ i ∈ Finset.Ico 1 b, (n / 3 ^ i + 3 * ((n + 1) / 3 ^ i))
                ≤ ∑ i ∈ Finset.Ico 1 b, ((4 * n) / 3 ^ i + if i = 1 then 1 else 0) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
              split_ifs with hi_eq
              · subst hi_eq
                rw [pow_one]
                omega
              · rw [add_zero]
                have hi2 : 2 ≤ i := by omega
                have hpow : 4 ≤ 3 ^ i := by
                  calc 4 ≤ 3 ^ 2 := by norm_num
                    _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
                exact term_le_of_four_le hpow
            _ = (∑ i ∈ Finset.Ico 1 b, (4 * n) / 3 ^ i) + 1 := by
              rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
              simp [h1mem]
        · have hp4 : 4 ≤ p := by
            have hp2le := hp.two_le
            omega
          have hNf : (4 * n).factorial.factorization p ≤ N.factorization p := by
            rw [show N = 3 * (4 * n).factorial from rfl,
              Nat.factorization_mul (by decide) (Nat.factorial_ne_zero _),
              Finsupp.coe_add, Pi.add_apply]
            exact Nat.le_add_left _ _
          refine le_trans ?_ hNf
          rw [hDf, h4f]
          refine Finset.sum_le_sum fun i hi => ?_
          have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
          have hpow : 4 ≤ p ^ i :=
            le_trans hp4 (Nat.le_self_pow (by omega) p)
          exact term_le_of_four_le hpow
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hmul : D * OMA.S_oeis_a361033.a n = N := by
    dsimp [OMA.S_oeis_a361033.a]
    exact Nat.mul_div_cancel' hdvd
  have ha0 : OMA.S_oeis_a361033.a n ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact hN0 hmul.symm
  have ha_fac2 : (OMA.S_oeis_a361033.a n).factorization 2 =
      3 * ((Nat.digits 2 (n + 1)).sum - 1) := by
    have hmul_fac := congrArg (fun x => x.factorization 2) hmul
    rw [Nat.factorization_mul hD0 ha0, Finsupp.coe_add, Pi.add_apply] at hmul_fac
    omega
  have hodd_iff : Odd (OMA.S_oeis_a361033.a n) ↔ (OMA.S_oeis_a361033.a n).factorization 2 = 0 := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd, Nat.factorization_eq_zero_iff _ 2]
    simp [Nat.prime_two, ha0]
  rw [hodd_iff, ha_fac2]
  have h3_iff : 3 * ((Nat.digits 2 (n + 1)).sum - 1) = 0 ↔ (Nat.digits 2 (n + 1)).sum = 1 := by
    omega
  rw [h3_iff, sum_digits_two_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩
