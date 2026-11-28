import OMAStatements.S_mo_315652

-- Problem: Roots of unity, vanishing sums and derivatives
-- Upstream: formal-conjectures statements/mo-315652.lean:0 (declaration OMA.S_mo_315652.main)
-- Credit: @yhay81 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Polynomial OMA.S_mo_315652

private lemma isCoprime_of_prime_not_dvd {p : ℕ} (hp : p.Prime) {x : ℤ} (hpx : ¬ (p : ℤ) ∣ x)
    (e : ℕ) : IsCoprime ((p ^ e : ℕ) : ℤ) x := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h1 : IsCoprime (p : ℤ) x := (hpz.irreducible.coprime_iff_not_dvd).mpr hpx
  simpa [Nat.cast_pow] using h1.pow_left (m := e)

private lemma int_dvd_iff_primeFactors_pow_dvd {n : ℕ} (hn : n ≠ 0) (M : ℤ) :
    ((n : ℤ) ∣ M) ↔ ∀ p ∈ n.primeFactors, ((p ^ (n.factorization p) : ℕ) : ℤ) ∣ M := by
  constructor
  · intro h p _
    exact dvd_trans (Int.ofNat_dvd.mpr (Nat.ordProj_dvd n p)) h
  · intro h
    have hprod : ∏ p ∈ n.primeFactors, ((p ^ (n.factorization p) : ℕ) : ℤ) = (n : ℤ) := by
      rw [← Nat.cast_prod, ← Nat.support_factorization]
      exact congrArg (Nat.cast (R := ℤ)) (Nat.prod_factorization_pow_eq_self hn)
    rw [← hprod]
    refine Finset.prod_dvd_of_coprime ?_ h
    intro p hp q hq hpq
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hq' : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hcop : Nat.Coprime (p ^ n.factorization p) (q ^ n.factorization q) :=
      ((Nat.coprime_primes hp' hq').mpr hpq).pow _ _
    exact hcop.isCoprime

private lemma mul_X_sub_one_geometric (n : ℕ) :
    (X - 1 : ℤ[X]) * geometric n = X ^ n - 1 := by
  unfold geometric
  rw [mul_comm]
  exact geom_sum_mul X n

private lemma iterate_derivative_X_sub_one_mul (k : ℕ) (f : ℤ[X]) :
    derivative^[k + 1] ((X - 1) * f) =
      (X - 1) * derivative^[k + 1] f + C ((k + 1 : ℕ) : ℤ) * derivative^[k] f := by
  induction k with
  | zero =>
    simp [derivative_mul, mul_comm, add_comm]
  | succ k ih =>
    rw [Function.iterate_succ_apply' derivative (k + 1), ih,
      derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_one,
      sub_zero, one_mul, derivative_C_mul,
      ← Function.iterate_succ_apply' derivative (k + 1),
      ← Function.iterate_succ_apply' derivative k]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

private lemma dvd_eval_iterate_derivative_of_not_dvd {n : ℕ} (hn : 1 ≤ n) {a : ℤ}
    (ha : a ^ n ≡ 1 [ZMOD (n : ℤ)]) {p e : ℕ} (hp : p.Prime) (hpe : p ^ e ∣ n)
    (hpa : ¬ (p : ℤ) ∣ a - 1) (k : ℕ) :
    ((p ^ e : ℕ) : ℤ) ∣ (derivative^[k] (geometric n)).eval a := by
  have hcop : IsCoprime ((p ^ e : ℕ) : ℤ) (a - 1) := isCoprime_of_prime_not_dvd hp hpa e
  have hpe_n : ((p ^ e : ℕ) : ℤ) ∣ (n : ℤ) := Int.ofNat_dvd.mpr hpe
  have hpe_an : ((p ^ e : ℕ) : ℤ) ∣ a ^ n - 1 := by
    have h1 : (n : ℤ) ∣ 1 - a ^ n := Int.modEq_iff_dvd.mp ha
    exact dvd_trans hpe_n (dvd_sub_comm.mp h1)
  induction k with
  | zero =>
    have h0 : (a - 1) * (geometric n).eval a = a ^ n - 1 := by
      have := congrArg (eval a) (mul_X_sub_one_geometric n)
      simpa [eval_mul, eval_sub, eval_X, eval_one, eval_pow] using this
    exact hcop.dvd_of_dvd_mul_left (h0 ▸ hpe_an)
  | succ k ih =>
    have hrel := congrArg (fun P => (derivative^[k + 1] P).eval a) (mul_X_sub_one_geometric n)
    rw [iterate_derivative_X_sub_one_mul, iterate_derivative_sub,
      iterate_derivative_one (Nat.succ_pos k), sub_zero,
      iterate_derivative_X_pow_eq_C_mul] at hrel
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_one, eval_C, eval_pow] at hrel
    have hdesc_dvd : n ∣ n.descFactorial (k + 1) := by
      have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
      rw [← hn1, Nat.succ_descFactorial_succ]
      exact dvd_mul_right _ _
    have hrhs : ((p ^ e : ℕ) : ℤ) ∣ ((n.descFactorial (k + 1) : ℕ) : ℤ) * a ^ (n - (k + 1)) :=
      dvd_mul_of_dvd_left (dvd_trans hpe_n (Int.ofNat_dvd.mpr hdesc_dvd)) _
    have hterm : ((p ^ e : ℕ) : ℤ) ∣ ((k + 1 : ℕ) : ℤ) * (derivative^[k] (geometric n)).eval a :=
      dvd_mul_of_dvd_right ih _
    have hmul : ((p ^ e : ℕ) : ℤ) ∣ (a - 1) * (derivative^[k + 1] (geometric n)).eval a := by
      rw [← dvd_add_left hterm, hrel]
      exact hrhs
    exact hcop.dvd_of_dvd_mul_left hmul

private lemma geometric_taylor (n : ℕ) :
    geometric n = ∑ j ∈ Finset.range n, C ((n.choose (j + 1) : ℕ) : ℤ) * (X - 1) ^ j := by
  have hne : (X - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have := congrArg (eval 0) h
    norm_num at this
  apply mul_left_cancel₀ hne
  rw [mul_X_sub_one_geometric, Finset.mul_sum]
  have hbin : (X : ℤ[X]) ^ n =
      ∑ m ∈ Finset.range (n + 1), (X - 1 : ℤ[X]) ^ m * 1 ^ (n - m) * (n.choose m : ℤ[X]) := by
    conv_lhs => rw [show (X : ℤ[X]) = (X - 1) + 1 by ring]
    exact add_pow (X - 1 : ℤ[X]) 1 n
  rw [Finset.sum_range_succ'] at hbin
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one] at hbin
  have hsub : (X : ℤ[X]) ^ n - 1 =
      ∑ j ∈ Finset.range n, (X - 1 : ℤ[X]) ^ (j + 1) * (n.choose (j + 1) : ℤ[X]) := by
    rw [hbin]
    ring
  rw [hsub]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [C_eq_natCast, pow_succ]
  ring

private lemma eval_iterate_derivative_geometric (n k : ℕ) (a : ℤ) :
    (derivative^[k] (geometric n)).eval a =
      ∑ j ∈ Finset.range n, ((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k) := by
  rw [geometric_taylor, iterate_derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_derivative_C_mul, show (X - 1 : ℤ[X]) = X - C 1 by simp,
    iterate_derivative_X_sub_pow, nsmul_eq_mul, eval_mul, eval_mul, eval_C, eval_natCast,
    eval_pow, eval_sub, eval_X, eval_C]
  push_cast
  ring

private lemma mul_add_le_pow {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    p * (m + 1) + (m + 2) ≤ p ^ (m + 2) := by
  induction m with
  | zero =>
    simp only [zero_add, mul_one, pow_succ, pow_zero, one_mul]
    nlinarith
  | succ m ih =>
    rw [pow_succ']
    have h1 : p * (p * (m + 1) + (m + 2)) ≤ p * p ^ (m + 2) := Nat.mul_le_mul_left p ih
    have h2 : 4 * (m + 1) ≤ p * p * (m + 1) := Nat.mul_le_mul_right (m + 1) (by nlinarith)
    nlinarith

private lemma pow_dvd_mul_factorial {p : ℕ} (hp : 1 ≤ p) (m : ℕ) :
    p ^ m ∣ (p * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hpos : 1 ≤ p * (m + 1) := by nlinarith
    have hsplit : (p * (m + 1)).factorial = p * (m + 1) * (p * (m + 1) - 1).factorial := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, Nat.factorial_succ]
      rw [Nat.sub_add_cancel hpos]
    rw [hsplit, pow_succ']
    refine mul_dvd_mul (dvd_mul_right p (m + 1)) ?_
    have hle : p * m ≤ p * (m + 1) - 1 := Nat.le_sub_one_of_lt (by nlinarith)
    exact dvd_trans ih (Nat.factorial_dvd_factorial hle)

private lemma ordProj_dvd_factorial_mul_pow {p k j : ℕ} (hp : p.Prime) (hkj : k < j) :
    p ^ ((j + 1).factorization p) ∣ k.factorial * p ^ (j - k) := by
  set r := (j + 1).factorization p
  by_cases hr : r ≤ j - k
  · exact dvd_mul_of_dvd_right (pow_dvd_pow p hr) _
  · have hr2 : 2 ≤ r := by omega
    set m := r - 2
    have hrm : r = m + 2 := by omega
    have hpr_le : p ^ r ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) (Nat.ordProj_dvd (j + 1) p)
    have hj_le : j + 1 ≤ k + r := by omega
    rw [hrm] at hpr_le hj_le
    have hpm_le : p * (m + 1) ≤ k := by
      have h1 := mul_add_le_pow hp.two_le m
      omega
    have hfac : p ^ (m + 1) ∣ k.factorial :=
      dvd_trans (pow_dvd_mul_factorial hp.one_le (m + 1)) (Nat.factorial_dvd_factorial hpm_le)
    have hpow : p ^ 1 ∣ p ^ (j - k) := pow_dvd_pow p (by omega)
    rw [hrm, show m + 2 = (m + 1) + 1 by omega, pow_add]
    exact mul_dvd_mul hfac hpow

private lemma higher_term_dvd {n k j p e : ℕ} {a : ℤ} (hn : 1 ≤ n) (hp : p.Prime)
    (hpe : p ^ e ∣ n) (hkj : k < j) (hpa : (p : ℤ) ∣ a - 1) :
    ((p ^ e : ℕ) : ℤ) ∣ ((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k) := by
  set r := (j + 1).factorization p
  set u := ordCompl[p] (j + 1)
  have hju : p ^ r * u = j + 1 := Nat.ordProj_mul_ordCompl_eq_self (j + 1) p
  have hpu : ¬ p ∣ u := Nat.not_dvd_ordCompl hp (Nat.succ_ne_zero j)
  have hid : (j + 1) * (n.choose (j + 1) * j.descFactorial k) =
      n * (n - 1).choose j * j.choose k * k.factorial := by
    have hch : n * (n - 1).choose j = n.choose (j + 1) * (j + 1) := by
      have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
      simpa [hn1] using Nat.add_one_mul_choose_eq (n - 1) j
    have hdf : j.descFactorial k = k.factorial * j.choose k :=
      Nat.descFactorial_eq_factorial_mul_choose j k
    rw [hdf]
    calc
      (j + 1) * (n.choose (j + 1) * (k.factorial * j.choose k))
          = (n.choose (j + 1) * (j + 1)) * j.choose k * k.factorial := by ring
      _ = n * (n - 1).choose j * j.choose k * k.factorial := by rw [← hch]
  have hdvd_nat : p ^ (e + r) ∣ n * k.factorial * p ^ (j - k) := by
    rw [pow_add, mul_assoc]
    exact mul_dvd_mul hpe (ordProj_dvd_factorial_mul_pow hp hkj)
  have hdvd_a : ((p ^ (j - k) : ℕ) : ℤ) ∣ (a - 1) ^ (j - k) := by
    rw [Nat.cast_pow]
    exact pow_dvd_pow_of_dvd hpa (j - k)
  have hdvd_prod : ((p ^ (e + r) : ℕ) : ℤ) ∣
      ((j + 1 : ℕ) : ℤ) * (((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k)) := by
    have hmul_eq : ((j + 1 : ℕ) : ℤ) *
        (((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k)) =
        ((n * k.factorial : ℕ) : ℤ) * (a - 1) ^ (j - k) * (((n - 1).choose j * j.choose k : ℕ) : ℤ) := by
      have hidz := congrArg (Nat.cast (R := ℤ)) hid
      push_cast at hidz ⊢
      linear_combination hidz * (a - 1) ^ (j - k)
    rw [hmul_eq]
    refine dvd_mul_of_dvd_left ?_ _
    have h1 : ((p ^ (e + r) : ℕ) : ℤ) ∣ ((n * k.factorial : ℕ) : ℤ) * ((p ^ (j - k) : ℕ) : ℤ) := by
      simpa [Nat.cast_mul] using Int.ofNat_dvd.mpr hdvd_nat
    exact dvd_trans h1 (mul_dvd_mul_left _ hdvd_a)
  have hdvd_u : ((p ^ e : ℕ) : ℤ) ∣
      (u : ℤ) * (((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k)) := by
    have hpr_ne : ((p ^ r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero r hp.ne_zero
    have hju_z : ((j + 1 : ℕ) : ℤ) = ((p ^ r : ℕ) : ℤ) * (u : ℤ) := by
      exact_mod_cast hju.symm
    rw [hju_z, pow_add, Nat.cast_mul] at hdvd_prod
    have h1 : ((p ^ r : ℕ) : ℤ) * ((p ^ e : ℕ) : ℤ) ∣
        ((p ^ r : ℕ) : ℤ) * ((u : ℤ) *
          (((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k))) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdvd_prod
    exact (mul_dvd_mul_iff_left hpr_ne).mp h1
  have hcop : IsCoprime ((p ^ e : ℕ) : ℤ) (u : ℤ) := by
    have hcopn : Nat.Coprime (p ^ e) u := (hp.coprime_iff_not_dvd.mpr hpu).pow_left e
    exact hcopn.isCoprime
  exact hcop.dvd_of_dvd_mul_left hdvd_u

private lemma dvd_eval_iff_leading_of_dvd {n k p e : ℕ} {a : ℤ} (hn : 1 ≤ n) (hkn : k < n)
    (hp : p.Prime) (hpe : p ^ e ∣ n) (hpa : (p : ℤ) ∣ a - 1) :
    ((p ^ e : ℕ) : ℤ) ∣ (derivative^[k] (geometric n)).eval a ↔
      p ^ e ∣ n.choose (k + 1) * k.factorial := by
  rw [eval_iterate_derivative_geometric]
  have hk_mem : k ∈ Finset.range n := Finset.mem_range.mpr hkn
  rw [← Finset.add_sum_erase _ _ hk_mem]
  have hrest : ((p ^ e : ℕ) : ℤ) ∣
      ∑ j ∈ (Finset.range n).erase k,
        ((n.choose (j + 1) * j.descFactorial k : ℕ) : ℤ) * (a - 1) ^ (j - k) := by
    refine Finset.dvd_sum fun j hj => ?_
    have hne : j ≠ k := Finset.ne_of_mem_erase hj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, mul_zero, Nat.cast_zero, zero_mul]
      exact dvd_zero _
    · exact higher_term_dvd hn hp hpe hgt hpa
  rw [dvd_add_left hrest, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, Int.ofNat_dvd]

private lemma succ_dvd_factorial_of_not_four_not_prime {k : ℕ} (h4 : k + 1 ≠ 4)
    (hp : ¬ (k + 1).Prime) : k + 1 ∣ k.factorial := by
  by_cases hk0 : k = 0
  · subst hk0; norm_num
  have h2 : 2 ≤ k + 1 := by omega
  set u := (k + 1).minFac
  have hu_prime : u.Prime := Nat.minFac_prime (by omega)
  have hu_dvd : u ∣ k + 1 := Nat.minFac_dvd (k + 1)
  have hu_sq : u ^ 2 ≤ k + 1 := Nat.minFac_sq_le_self (Nat.succ_pos k) hp
  obtain ⟨v, hv⟩ := hu_dvd
  have hu2 : 2 ≤ u := hu_prime.two_le
  have huv : u ≤ v := by nlinarith
  have hv_le : v ≤ k := by nlinarith
  by_cases heq : u = v
  · have hu3 : 3 ≤ u := by
      by_contra hlt
      have hu_eq : u = 2 := by omega
      rw [← heq, hu_eq] at hv
      exact h4 hv
    have h2u_le : 2 * u ≤ k := by nlinarith
    have hfac1 : u * (2 * u) ∣ (2 * u).factorial := by
      have hpos : 1 ≤ 2 * u := by omega
      have hsplit : (2 * u).factorial = 2 * u * (2 * u - 1).factorial := by
        conv_lhs => rw [← Nat.sub_add_cancel hpos, Nat.factorial_succ]
        rw [Nat.sub_add_cancel hpos]
      rw [hsplit, mul_comm]
      exact mul_dvd_mul_left (2 * u) (Nat.dvd_factorial (by omega) (by omega))
    have hu2_dvd : u * u ∣ u * (2 * u) := ⟨2, by ring⟩
    rw [hv, ← heq]
    exact dvd_trans (dvd_trans hu2_dvd hfac1) (Nat.factorial_dvd_factorial h2u_le)
  · have huv_lt : u < v := lt_of_le_of_ne huv heq
    have hfac : u * v ∣ v.factorial := by
      have hpos : 1 ≤ v := by omega
      have hsplit : v.factorial = v * (v - 1).factorial := by
        conv_lhs => rw [← Nat.sub_add_cancel hpos, Nat.factorial_succ]
        rw [Nat.sub_add_cancel hpos]
      rw [hsplit, mul_comm]
      exact mul_dvd_mul_left v (Nat.dvd_factorial (by omega) (by omega))
    rw [hv]
    exact dvd_trans hfac (Nat.factorial_dvd_factorial hv_le)

private lemma leading_dvd_of_not_four_not_prime {n k : ℕ} (hn : 1 ≤ n) (h4 : k + 1 ≠ 4)
    (hp : ¬ (k + 1).Prime) : n ∣ n.choose (k + 1) * k.factorial := by
  obtain ⟨q, hq⟩ := succ_dvd_factorial_of_not_four_not_prime h4 hp
  have hch : n * (n - 1).choose k = n.choose (k + 1) * (k + 1) := by
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [hn1] using Nat.add_one_mul_choose_eq (n - 1) k
  have heq : (k + 1) * (n.choose (k + 1) * k.factorial) =
      (k + 1) * (n * (n - 1).choose k * q) := by
    calc
      (k + 1) * (n.choose (k + 1) * k.factorial)
          = (n.choose (k + 1) * (k + 1)) * k.factorial := by ring
      _ = n * (n - 1).choose k * ((k + 1) * q) := by rw [← hch, hq]
      _ = (k + 1) * (n * (n - 1).choose k * q) := by ring
  have hval : n.choose (k + 1) * k.factorial = n * ((n - 1).choose k * q) := by
    have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) heq
    linarith
  exact ⟨(n - 1).choose k * q, hval⟩

private lemma leading_dvd_of_coprime {n k p e : ℕ} (hn : 1 ≤ n) (hpe : p ^ e ∣ n)
    (hcop : Nat.Coprime (p ^ e) (k + 1)) : p ^ e ∣ n.choose (k + 1) * k.factorial := by
  have hch : n * (n - 1).choose k = n.choose (k + 1) * (k + 1) := by
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simpa [hn1] using Nat.add_one_mul_choose_eq (n - 1) k
  have hmul : p ^ e ∣ (k + 1) * (n.choose (k + 1) * k.factorial) := by
    have : (k + 1) * (n.choose (k + 1) * k.factorial) = n * ((n - 1).choose k * k.factorial) := by
      calc
        (k + 1) * (n.choose (k + 1) * k.factorial)
            = (n.choose (k + 1) * (k + 1)) * k.factorial := by ring
        _ = n * ((n - 1).choose k * k.factorial) := by rw [← hch]; ring
    rw [this]
    exact dvd_mul_of_dvd_left hpe _
  exact hcop.dvd_of_dvd_mul_left hmul

private lemma leading_not_dvd_prime {n k : ℕ} (hkn : k < n) (hp : (k + 1).Prime)
    (hdvd : k + 1 ∣ n) :
    ¬ (k + 1) ^ (n.factorization (k + 1)) ∣ n.choose (k + 1) * k.factorial := by
  set p := k + 1
  set e := n.factorization p
  set m := ordCompl[p] n
  have hn0 : n ≠ 0 := by omega
  have hnm : p ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn0
  intro hdiv
  have hdesc : p * (n.choose p * k.factorial) = n * (n - 1).descFactorial k := by
    have hfac : p * k.factorial = p.factorial := by
      change (k + 1) * k.factorial = (k + 1).factorial
      exact (Nat.factorial_succ k).symm
    have h1' : p * (n.choose p * k.factorial) = n.descFactorial p := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, ← hfac]
      ring
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    rw [h1']
    conv_lhs => rw [← hn1]
    change (n - 1 + 1).descFactorial (k + 1) = n * (n - 1).descFactorial k
    rw [Nat.succ_descFactorial_succ, hn1]
  have h1 : p ^ e * p ∣ p ^ e * (m * (n - 1).descFactorial k) := by
    calc
      p ^ e * p ∣ p * (n.choose p * k.factorial) := by
        rw [mul_comm (p ^ e) p]
        exact mul_dvd_mul_left p hdiv
      _ = n * (n - 1).descFactorial k := hdesc
      _ = p ^ e * (m * (n - 1).descFactorial k) := by rw [← hnm, mul_assoc]
  have hpe_ne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have h2 : p ∣ m * (n - 1).descFactorial k := (mul_dvd_mul_iff_left hpe_ne).mp h1
  have h3 : p ∣ (n - 1).descFactorial k := (hp.dvd_mul.mp h2).resolve_left hpm
  rw [Nat.descFactorial_eq_prod_range] at h3
  obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h3
  have hik : i < k := Finset.mem_range.mp hi
  have hsum : (n - 1 - i) + (i + 1) = n := by omega
  have hpi1 : p ∣ i + 1 := by
    rw [← hsum] at hdvd
    exact (Nat.dvd_add_right hpi).mp hdvd
  have hle : p ≤ i + 1 := Nat.le_of_dvd (Nat.succ_pos i) hpi1
  omega

private lemma leading_not_dvd_four {n : ℕ} (h4 : 4 ∣ n) (hn : 1 ≤ n) :
    ¬ 2 ^ (n.factorization 2) ∣ n.choose 4 * (3 : ℕ).factorial := by
  set e := n.factorization 2
  set m := ordCompl[2] n
  have hn0 : n ≠ 0 := by omega
  have hn4 : 4 ≤ n := Nat.le_of_dvd (by omega) h4
  have hnm : 2 ^ e * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have h2m : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn0
  intro hdiv
  have hdesc : 4 * (n.choose 4 * (3 : ℕ).factorial) = n * ((n - 1) * (n - 2) * (n - 3)) := by
    have h1' : 4 * (n.choose 4 * (3 : ℕ).factorial) = n.descFactorial 4 := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      change 4 * (n.choose 4 * 6) = 24 * n.choose 4
      ring
    rw [h1', Nat.descFactorial_eq_prod_range]
    simp [Finset.prod_range_succ]
    ring
  have h1 : 2 ^ e * 4 ∣ 2 ^ e * (m * ((n - 1) * (n - 2) * (n - 3))) := by
    calc
      2 ^ e * 4 ∣ 4 * (n.choose 4 * (3 : ℕ).factorial) := by
        rw [mul_comm (2 ^ e) 4]
        exact mul_dvd_mul_left 4 hdiv
      _ = n * ((n - 1) * (n - 2) * (n - 3)) := hdesc
      _ = 2 ^ e * (m * ((n - 1) * (n - 2) * (n - 3))) := by rw [← hnm, mul_assoc]
  have h2 : 4 ∣ m * ((n - 1) * (n - 2) * (n - 3)) :=
    (mul_dvd_mul_iff_left (pow_ne_zero e (by decide : (2 : ℕ) ≠ 0))).mp h1
  have hodd : Nat.Coprime 4 (m * (n - 1) * (n - 3)) := by
    have hm_odd : m % 2 = 1 := by omega
    have hn_mod : n % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h4
    have h1odd : (m * (n - 1) * (n - 3)) % 2 = 1 := by
      have ha : (n - 1) % 2 = 1 := by omega
      have hb : (n - 3) % 2 = 1 := by omega
      simp [Nat.mul_mod, hm_odd, ha, hb]
    have hcop2 : Nat.Coprime 2 (m * (n - 1) * (n - 3)) := by
      rw [Nat.prime_two.coprime_iff_not_dvd]
      omega
    simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow_left 2
  have h3 : 4 ∣ m * (n - 1) * (n - 3) * (n - 2) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using h2
  have h4n2 : 4 ∣ n - 2 := hodd.dvd_of_dvd_mul_left h3
  omega

private lemma leading_dvd_four_of_not_dvd {n : ℕ} (h4 : ¬ 4 ∣ n) :
    2 ^ (n.factorization 2) ∣ n.choose 4 * (3 : ℕ).factorial := by
  have he : n.factorization 2 ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ n.factorization 2 := by omega
    have : 2 ^ 2 ∣ n := dvd_trans (pow_dvd_pow 2 h2) (Nat.ordProj_dvd n 2)
    exact h4 (by simpa using this)
  have hpow : 2 ^ n.factorization 2 ∣ 2 := by
    simpa using pow_dvd_pow 2 he
  exact dvd_mul_of_dvd_right (dvd_trans hpow (by norm_num : 2 ∣ (3 : ℕ).factorial)) _

private lemma two_dvd_sub_one_of_four_dvd {n : ℕ} (hn : 1 ≤ n) (h4 : 4 ∣ n) {a : ℤ}
    (ha : a ^ n ≡ 1 [ZMOD (n : ℤ)]) : (2 : ℤ) ∣ a - 1 := by
  have h2n : (2 : ℤ) ∣ (n : ℤ) := Int.ofNat_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) h4)
  have h2an : (2 : ℤ) ∣ a ^ n - 1 := dvd_trans h2n (dvd_sub_comm.mp (Int.modEq_iff_dvd.mp ha))
  by_contra hnot
  have h2a : (2 : ℤ) ∣ a := by omega
  have h2ap : (2 : ℤ) ∣ a ^ n := dvd_pow h2a (by omega)
  have h21 : (2 : ℤ) ∣ 1 := by
    have : (2 : ℤ) ∣ a ^ n - (a ^ n - 1) := dvd_sub h2ap h2an
    simp at this
  omega

theorem OMA.solution : type_of% @OMA.S_mo_315652.main := by
  intro n k hn hkn a ha
  have hn0 : n ≠ 0 := by omega
  rcases eq_or_lt_of_le hkn with rfl | hlt
  · have hzero : (derivative^[k] (geometric k)).eval a = 0 := by
      rw [eval_iterate_derivative_geometric]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hj), mul_zero,
        Nat.cast_zero, zero_mul]
    rw [hzero]
    simp only [dvd_zero, true_iff]
    by_cases h4 : k + 1 = 4
    · right; left
      exact ⟨h4, by omega⟩
    · by_cases hp : (k + 1).Prime
      · right; right
        refine ⟨hp, Or.inl ?_⟩
        intro hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      · left
        exact ⟨h4, hp⟩
  · rw [int_dvd_iff_primeFactors_pow_dvd hn0]
    by_cases h4 : k + 1 = 4
    · have hk3 : k = 3 := by omega
      have hnp4 : ¬ Nat.Prime 4 := by decide
      simp only [h4, hnp4, ne_eq, not_true_eq_false, false_and, true_and, false_or, or_false]
      constructor
      · intro hall h4n
        have h2mem : 2 ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num : 2 ∣ 4) h4n, hn0⟩
        have h2a : (2 : ℤ) ∣ a - 1 := two_dvd_sub_one_of_four_dvd hn h4n ha
        have h2div := hall 2 h2mem
        rw [dvd_eval_iff_leading_of_dvd hn hlt Nat.prime_two (Nat.ordProj_dvd n 2) h2a,
          hk3] at h2div
        exact leading_not_dvd_four h4n hn h2div
      · intro hnot4 p hp
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        by_cases hpa : (p : ℤ) ∣ a - 1
        · rw [dvd_eval_iff_leading_of_dvd hn hlt hp' (Nat.ordProj_dvd n p) hpa]
          by_cases hp2 : p = 2
          · subst hp2
            rw [hk3]
            exact leading_dvd_four_of_not_dvd hnot4
          · refine leading_dvd_of_coprime hn (Nat.ordProj_dvd n p) ?_
            rw [h4]
            have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp' Nat.prime_two).mpr hp2
            simpa [show (4 : ℕ) = 2 ^ 2 by norm_num] using hcop2.pow (n.factorization p) 2
        · exact dvd_eval_iterate_derivative_of_not_dvd hn ha hp' (Nat.ordProj_dvd n p) hpa k
    · by_cases hkp : (k + 1).Prime
      · simp only [h4, hkp, not_true_eq_false, and_false, false_and, false_or, true_and]
        constructor
        · intro hall
          by_cases hdvd : k + 1 ∣ n
          · right
            intro hmod
            have hpa : ((k + 1 : ℕ) : ℤ) ∣ a - 1 := dvd_sub_comm.mp (Int.modEq_iff_dvd.mp hmod)
            have hmem : k + 1 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hkp, hdvd, hn0⟩
            have hdiv := hall (k + 1) hmem
            rw [dvd_eval_iff_leading_of_dvd hn hlt hkp (Nat.ordProj_dvd n (k + 1)) hpa] at hdiv
            exact leading_not_dvd_prime hlt hkp hdvd hdiv
          · exact Or.inl hdvd
        · intro hcond p hp
          have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
          by_cases hpeq : p = k + 1
          · subst hpeq
            rcases hcond with hndvd | hnmod
            · exact absurd (Nat.dvd_of_mem_primeFactors hp) hndvd
            · have hpa : ¬ ((k + 1 : ℕ) : ℤ) ∣ a - 1 := fun h =>
                hnmod (Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp h))
              exact dvd_eval_iterate_derivative_of_not_dvd hn ha hp'
                (Nat.ordProj_dvd n (k + 1)) hpa k
          · by_cases hpa : (p : ℤ) ∣ a - 1
            · rw [dvd_eval_iff_leading_of_dvd hn hlt hp' (Nat.ordProj_dvd n p) hpa]
              refine leading_dvd_of_coprime hn (Nat.ordProj_dvd n p) ?_
              exact ((Nat.coprime_primes hp' hkp).mpr hpeq).pow_left _
            · exact dvd_eval_iterate_derivative_of_not_dvd hn ha hp'
                (Nat.ordProj_dvd n p) hpa k
      · simp only [h4, hkp, ne_eq, not_false_eq_true, and_self, true_or, iff_true]
        intro p hp
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        by_cases hpa : (p : ℤ) ∣ a - 1
        · rw [dvd_eval_iff_leading_of_dvd hn hlt hp' (Nat.ordProj_dvd n p) hpa]
          exact dvd_trans (Nat.ordProj_dvd n p) (leading_dvd_of_not_four_not_prime hn h4 hkp)
        · exact dvd_eval_iterate_derivative_of_not_dvd hn ha hp' (Nat.ordProj_dvd n p) hpa k
