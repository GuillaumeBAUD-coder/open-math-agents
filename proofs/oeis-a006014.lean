import OMAStatements.S_oeis_a006014

namespace OMA.A006014
open S_oeis_a006014 Finset

private lemma first_size (n : ℕ) : (firstTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [firstTable, ih, Nat.add_assoc]

private lemma second_size (n : ℕ) : (secondTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [secondTable]
    split <;> simp [ih]

private lemma first_get (n i : ℕ) (h : i ≤ n) :
    (firstTable n).getD i 0 = a006014 i := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    by_cases h' : i = n + 1
    · subst i; rfl
    cases n with
    | zero =>
      have : i = 0 := by omega
      subst i; rfl
    | succ n =>
      rw [firstTable]
      have hlt : i < (firstTable (n + 1)).size := by rw [first_size]; omega
      simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push,
        if_neg (Nat.ne_of_lt hlt)] using ih (by omega)

private lemma second_get (n i : ℕ) (h : i ≤ n) :
    (secondTable n).getD i 0 = a379818 i := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    subst i; rfl
  | succ n ih =>
    by_cases h' : i = n + 1
    · subst i; rfl
    have hlt : i < (secondTable n).size := by rw [second_size]; omega
    rw [secondTable]
    split <;>
      simpa only [Array.getD_eq_getD_getElem?, Array.getElem?_push,
        if_neg (Nat.ne_of_lt hlt)] using ih (by omega)

private lemma a_recur (n : ℕ) :
    a006014 (n + 2) = (n + 2) * a006014 (n + 1) +
      ∑ i ∈ range n, a006014 (i + 1) * a006014 (n - i) := by
  change (firstTable (n + 2)).getD (n + 2) 0 = _
  rw [firstTable]
  have hs : (firstTable (n + 1)).size = n + 2 := first_size _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos hs.symm, Option.getD_some,
    first_get _ _ (by omega : n + 1 ≤ n + 1)]
  congr 1
  apply sum_congr rfl
  intro i hi
  have hp := mem_range.mp hi
  change (firstTable (n + 1)).getD (i + 1) 0 *
      (firstTable (n + 1)).getD (n - i) 0 = a006014 (i + 1) * a006014 (n - i)
  rw [first_get _ _ (by omega), first_get _ _ (by omega)]

private lemma a025_le (n : ℕ) : a025480 n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [a025480]
    split
    · omega
    · exact (ih (n / 2) (by omega)).trans (by omega)

private lemma f_odd (k : ℕ) : a379818 (2 * k + 1) = a379818 k := by
  have hs : (secondTable (2 * k)).size = 2 * k + 1 := second_size _
  change (secondTable (2 * k + 1)).getD (2 * k + 1) 0 = _
  rw [secondTable]
  simp only [show (2 * k + 1) % 2 = 1 by omega, if_true,
    show (2 * k + 1) / 2 = k by omega]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos hs.symm, Option.getD_some]
  exact second_get (2 * k) k (by omega)

private lemma f_even (k : ℕ) (hk : 0 < k) :
    let d := 2 ^ k.factorization 2
    a379818 (2 * k) =
      a379818 k + a379818 (k - d) + a379818 (2 * k - d) + a379818 (a025480 (k - 1)) := by
  dsimp only
  change (secondTable (2 * k)).getD (2 * k) 0 = _
  have heq : 2 * k = (2 * k - 1) + 1 := by omega
  conv_lhs => rw [heq, secondTable]
  have hm : (2 * k) % 2 ≠ 1 := by omega
  have hdiv : (2 * k) / 2 = k := by omega
  simp only [← heq, if_neg hm, hdiv]
  have hs : (secondTable (2 * k - 1)).size = 2 * k := by rw [second_size]; omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos hs.symm, Option.getD_some]
  have ha := a025_le (k - 1)
  have hd : 0 < 2 ^ k.factorization 2 := by positivity
  change (secondTable (2 * k - 1)).getD k 0 +
    (secondTable (2 * k - 1)).getD (k - 2 ^ k.factorization 2) 0 +
    (secondTable (2 * k - 1)).getD (2 * k - 2 ^ k.factorization 2) 0 +
    (secondTable (2 * k - 1)).getD (a025480 (k - 1)) 0 = _
  rw [second_get _ k (by omega), second_get _ (k - 2 ^ k.factorization 2) (by omega),
    second_get _ (2 * k - 2 ^ k.factorization 2) (by omega),
    second_get _ (a025480 (k - 1)) (by omega)]

private lemma a025_dyadic (j k : ℕ) :
    a025480 (2 ^ j * (2 * k + 1) - 1) = k := by
  induction j with
  | zero =>
    rw [a025480]
    simp
  | succ j ih =>
    have hp : 0 < 2 ^ j * (2 * k + 1) := by positivity
    rw [pow_succ, show 2 ^ j * 2 * (2 * k + 1) = 2 * (2 ^ j * (2 * k + 1)) by ring]
    rw [a025480, if_neg (by omega), show (2 * (2 ^ j * (2 * k + 1)) - 1) / 2 =
      2 ^ j * (2 * k + 1) - 1 by omega, ih]

private lemma f_dyadic (j k : ℕ) :
    a379818 (2 ^ (j + 1) * (2 * k + 1)) =
      a379818 (2 ^ j * (2 * k + 1)) + a379818 (2 ^ (j + 1) * k) +
      a379818 (2 ^ j * (2 * (2 * k) + 1)) + a379818 k := by
  have hk : 0 < 2 ^ j * (2 * k + 1) := by positivity
  have hv : (2 ^ j * (2 * k + 1)).factorization 2 = j := by
    rw [Nat.factorization_mul (by positivity) (by omega : 2 * k + 1 ≠ 0)]
    simp [Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd
      (by omega : ¬ 2 ∣ 2 * k + 1)]
  have h := f_even (2 ^ j * (2 * k + 1)) hk
  dsimp only at h
  rw [hv, a025_dyadic] at h
  rw [show 2 * (2 ^ j * (2 * k + 1)) = 2 ^ (j + 1) * (2 * k + 1) by ring_nf,
    show 2 ^ j * (2 * k + 1) - 2 ^ j = 2 ^ (j + 1) * k by
      rw [mul_add, mul_one, Nat.add_sub_cancel, pow_succ]; ring,
    show 2 ^ (j + 1) * (2 * k + 1) - 2 ^ j = 2 ^ j * (2 * (2 * k) + 1) by
      rw [show 2 ^ (j + 1) * (2 * k + 1) = 2 ^ j * (2 * (2 * k) + 1) + 2 ^ j by ring,
        Nat.add_sub_cancel]] at h
  exact h

private def shift (u : ℕ → ℚ) (i : ℕ) : ℚ := u (i + 1)

private def prepend (u : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | i + 1 => u i

private def bt (j : ℕ) (u : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range (j + 1), (j.choose i : ℚ) * u i

private lemma bt_succ (j : ℕ) (u : ℕ → ℚ) :
    bt (j + 1) u = bt j u + bt j (shift u) := by
  simpa [bt, shift, Nat.add_assoc] using sum_choose_succ_mul (fun i _ => u i) j

private lemma bt_prepend_shift (j : ℕ) (u : ℕ → ℚ) :
    bt j u = u 0 + bt j (prepend (shift u)) := by
  simp only [bt, sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul, prepend,
    shift, add_zero, mul_zero]
  ac_rfl

private def expr (j : ℕ) (u : ℕ → ℚ) : ℚ :=
  bt (j + 2) (prepend u) - u (j + 1) - bt j u

private lemma expr_succ (j : ℕ) (u : ℕ → ℚ) :
    expr (j + 1) u = expr j u + u (j + 1) + expr j (shift u) + u 0 := by
  have hshift : shift (prepend u) = u := rfl
  unfold expr
  rw [show j + 1 + 2 = j + 2 + 1 by omega, bt_succ (j + 2), bt_succ j, hshift,
    bt_prepend_shift (j + 2) u]
  unfold shift
  ring

private def dyad (k j : ℕ) : ℚ := a379818 (2 ^ j * k)

private lemma dyad_step (j k : ℕ) :
    (a379818 (2 ^ j * (2 * k + 1)) : ℚ) = expr j (dyad k) := by
  induction j generalizing k with
  | zero => simp [f_odd, expr, bt, prepend, dyad, Finset.sum_range_succ]; ring
  | succ j ih =>
    rw [f_dyadic, expr_succ, Nat.cast_add, Nat.cast_add, Nat.cast_add, ih, ih]
    have h : dyad (2 * k) = shift (dyad k) := by
      funext i
      simp only [dyad, shift, pow_succ, mul_assoc]
    rw [h]
    simp [dyad]

private lemma pair_sum (u : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ range (2 * n), u i) =
      (∑ i ∈ range n, u (2 * i)) + ∑ i ∈ range n, u (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    simp only [sum_range_succ, ih]
    ring

private def prefixSum (m j : ℕ) : ℚ := ∑ k ∈ range (2 ^ m), dyad k j

private lemma prefix_zero : prefixSum 0 = fun _ => 1 := by
  funext j
  simp [prefixSum, dyad]
  rfl

private def step : Module.End ℚ (ℕ → ℚ) where
  toFun u j := bt (j + 2) (prepend u) - bt j u
  map_add' u v := by
    funext j
    have h (i : ℕ) : prepend (u + v) i = prepend u i + prepend v i := by
      cases i <;> simp [prepend]
    simp only [bt, Pi.add_apply, h, mul_add, sum_add_distrib]
    ring
  map_smul' c u := by
    funext j
    have h (i : ℕ) : prepend (c • u) i = c * prepend u i := by
      cases i <;> simp [prepend, smul_eq_mul]
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, bt, h, mul_left_comm _ c,
      ← mul_sum]
    ring

private lemma prefix_succ (m : ℕ) : prefixSum (m + 1) = step (prefixSum m) := by
  funext j
  change (∑ k ∈ range (2 ^ (m + 1)), dyad k j) = _
  rw [pow_succ', pair_sum]
  have heven (k : ℕ) : dyad (2 * k) j = dyad k (j + 1) := by simp [dyad, pow_succ, mul_assoc]
  simp only [heven, show ∀ k, dyad (2 * k + 1) j = expr j (dyad k) from
    fun k => dyad_step j k]
  have hprep (i : ℕ) : prepend (prefixSum m) i = ∑ k ∈ range (2 ^ m), prepend (dyad k) i := by
    cases i <;> simp [prepend, prefixSum]
  simp only [expr, sum_sub_distrib, step, LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (∑ k ∈ range (2 ^ m), dyad k (j + 1)) = prefixSum m (j + 1) by rfl]
  have hB (q : ℕ) :
      (∑ k ∈ range (2 ^ m), bt q (dyad k)) = bt q (prefixSum m) := by
    simp only [bt, prefixSum, mul_sum, sum_comm (s := range (2 ^ m))]
  have hP (q : ℕ) :
      (∑ k ∈ range (2 ^ m), bt q (prepend (dyad k))) = bt q (prepend (prefixSum m)) := by
    simp only [bt, hprep, mul_sum, sum_comm (s := range (2 ^ m))]
  rw [hB, hP]
  ring

private def geo (t : ℚ) (j : ℕ) : ℚ := t ^ j

private lemma bt_geo (t : ℚ) (j : ℕ) : bt j (geo t) = (1 + t) ^ j := by
  rw [add_comm, add_pow]
  simp [bt, geo, mul_comm]

private lemma bt_geo_prepend (t : ℚ) (j : ℕ) :
    t * bt j (prepend (geo t)) = bt j (geo t) - 1 := by
  have h (i : ℕ) : t * prepend (geo t) i = prepend (shift (geo t)) i := by
    cases i <;> simp [prepend, shift, geo, pow_succ']
  simp only [bt, mul_sum, mul_left_comm t, h]
  rw [show (∑ i ∈ range (j + 1), (j.choose i : ℚ) * prepend (shift (geo t)) i) =
    bt j (prepend (shift (geo t))) by rfl]
  change bt j (prepend (shift (geo t))) = bt j (geo t) - 1
  linarith [bt_prepend_shift j (geo t), show geo t 0 = 1 by simp [geo]]

private lemma step_geo (t : ℚ) (ht : t ≠ 0) :
    step (geo t) = (t + 1 + 1 / t) • geo (t + 1) - (1 / t) • geo 1 := by
  funext j
  change bt (j + 2) (prepend (geo t)) - bt j (geo t) =
    (t + 1 + 1 / t) * (t + 1) ^ j - (1 / t) * 1 ^ j
  rw [bt_geo, show bt (j + 2) (prepend (geo t)) = ((1 + t) ^ (j + 2) - 1) / t by
    apply (eq_div_iff ht).mpr
    rw [mul_comm, bt_geo_prepend, bt_geo], pow_add, one_pow, add_comm 1 t]
  field_simp
  ring

private def alpha (t : ℕ) : ℚ := (t : ℚ) + 1 + 1 / (t : ℚ)

private def run (n t : ℕ) : ℚ := ((step ^ n) (geo (t : ℚ))) 0

private lemma run_zero (t : ℕ) : run 0 t = 1 := by
  simp [run, geo]

private lemma run_succ (n t : ℕ) (ht : 0 < t) :
    run (n + 1) t = alpha t * run n (t + 1) - (1 / (t : ℚ)) * run n 1 := by
  have ht' : (t : ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [run, pow_succ, Module.End.mul_apply, step_geo _ ht', map_sub, map_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, alpha, Nat.cast_add, Nat.cast_one]

private lemma prefix_run (n : ℕ) : prefixSum n 0 = run n 1 := by
  have h (n : ℕ) : prefixSum n = (step ^ n) (geo 1) := by
    induction n with
    | zero =>
      rw [prefix_zero, pow_zero, Module.End.one_apply]
      funext i
      simp [geo]
    | succ n ih => rw [prefix_succ, ih, pow_succ', Module.End.mul_apply]
  rw [h]
  simp [run]

private def path (n t : ℕ) : ℚ := ∏ i ∈ range n, alpha (t + i)

private lemma path_head (n t : ℕ) : path (n + 1) t = alpha t * path n (t + 1) := by
  simp only [path, prod_range_succ', add_zero, ← add_assoc]
  ac_rfl

private lemma path_last (n t : ℕ) : path (n + 1) t = path n t * alpha (t + n) := by
  simp [path, prod_range_succ]

-- Expand a walk according to the position of its first return to state one.
private lemma run_expansion (n t : ℕ) (ht : 0 < t) :
    run n t = path n t -
      ∑ i ∈ range n, path i t / (t + i : ℕ) * run (n - (i + 1)) 1 := by
  induction n generalizing t with
  | zero => simp [run_zero, path]
  | succ n ih =>
    rw [run_succ _ _ ht, ih (t + 1) (by omega), path_head, sum_range_succ']
    have hzero : path 0 t = 1 := by simp [path]
    simp only [hzero, add_zero, Nat.add_sub_cancel, mul_sub, mul_sum]
    have hsum :
        (∑ i ∈ range n, alpha t *
            (path i (t + 1) / (↑(t + 1 + i) : ℚ) * run (n - (i + 1)) 1)) =
          ∑ i ∈ range n, path (i + 1) t / (↑(t + (i + 1)) : ℚ) *
            run (n + 1 - ((i + 1) + 1)) 1 := by
      apply sum_congr rfl
      intro i _
      rw [path_head, show t + (i + 1) = t + 1 + i by omega,
        show n + 1 - ((i + 1) + 1) = n - (i + 1) by omega]
      ring
    rw [hsum]
    ring

open PowerSeries

private def qCoeff : ℕ → ℚ
  | 0 => 1
  | n + 1 => path n 1 / (↑(n + 1) : ℚ)

private noncomputable def qSeries : PowerSeries ℚ := mk qCoeff
private noncomputable def fSeries : PowerSeries ℚ := mk (fun n => run n 1)
private noncomputable def pSeries : PowerSeries ℚ := mk (fun n => path n 1)

private lemma qCoeff_recur (n : ℕ) :
    (↑(n + 1) : ℚ) * qCoeff (n + 1) =
      ((n : ℚ)^2 + n + 1) * qCoeff n := by
  cases n with
  | zero => simp [qCoeff, path]
  | succ n =>
    simp only [qCoeff]
    rw [path_last]
    simp only [alpha, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

private lemma derivative_q : derivative ℚ qSeries = pSeries := by
  ext n
  simp only [coeff_derivative, qSeries, pSeries, qCoeff, coeff_mk]
  rw [show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by exact Nat.cast_succ n]
  exact div_mul_cancel₀ _ (show (n : ℚ) + 1 ≠ 0 by positivity)

private lemma multiply_q : qSeries * fSeries = pSeries := by
  ext n
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i qSeries * coeff j fSeries), sum_range_succ']
  simp only [qSeries, fSeries, pSeries, coeff_mk, qCoeff, Nat.sub_zero, one_mul]
  have h := run_expansion n 1 (by decide)
  simp only [Nat.cast_add, Nat.cast_one, add_comm 1] at h ⊢
  linarith

private lemma q_ne_zero : qSeries ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  norm_num [qSeries, qCoeff] at this

private lemma q_equation :
    derivative ℚ qSeries =
      qSeries + 2 * (X * derivative ℚ qSeries) +
        X ^ 2 * derivative ℚ (derivative ℚ qSeries) := by
  ext n
  have hx : coeff n (X * derivative ℚ qSeries) = (n : ℚ) * qCoeff n := by
    cases n with
    | zero => simp
    | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp [qSeries, mul_comm]
  have hx2 : coeff n (X ^ 2 * derivative ℚ (derivative ℚ qSeries)) =
      ((n : ℚ) * ((n : ℚ) - 1)) * qCoeff n := by
    cases n with
    | zero => simp [coeff_X_pow_mul']
    | succ n =>
      cases n with
      | zero => norm_num [coeff_X_pow_mul']
      | succ n =>
        rw [show n + 1 + 1 = n + 2 by omega,
          coeff_X_pow_mul (derivative ℚ (derivative ℚ qSeries)) 2 n,
          coeff_derivative, coeff_derivative]
        simp only [qSeries, coeff_mk, show n + 1 + 1 = n + 2 by omega]
        push_cast
        ring
  have h2 (y : PowerSeries ℚ) : coeff n (2 * y) = 2 * coeff n y := by
    rw [two_mul, map_add, two_mul]
  simp only [map_add, h2, hx, hx2]
  simp only [coeff_derivative, qSeries, coeff_mk]
  have h := qCoeff_recur n
  rw [show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by exact Nat.cast_succ n] at h
  linear_combination h

private lemma f_equation :
    fSeries = 1 + 2 * (X * fSeries) +
      X ^ 2 * (derivative ℚ fSeries + fSeries ^ 2) := by
  have hQ : derivative ℚ qSeries = qSeries * fSeries := derivative_q.trans multiply_q.symm
  have hD : derivative ℚ (derivative ℚ qSeries) =
      derivative ℚ qSeries * fSeries + qSeries * derivative ℚ fSeries := by
    rw [hQ, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [hQ]
    ring
  have h := q_equation
  nth_rewrite 1 [hQ] at h
  rw [hD, hQ] at h
  apply mul_left_cancel₀ q_ne_zero
  linear_combination h

private lemma run_recur (n : ℕ) :
    run (n + 1) 1 = (↑(n + 2) : ℚ) * run n 1 +
      ∑ i ∈ range n, run i 1 * run (n - (i + 1)) 1 := by
  have h := congrArg (coeff (n + 1)) f_equation
  have h2 (d : ℕ) (y : PowerSeries ℚ) : coeff d (2 * y) = 2 * coeff d y := by
    rw [two_mul, map_add, two_mul]
  cases n with
  | zero =>
    norm_num [h2, fSeries, coeff_succ_X_mul, coeff_X_pow_mul'] at h ⊢
    linarith
  | succ n =>
    simp only [map_add, h2, coeff_succ_X_mul, coeff_X_pow_mul',
      if_pos (show (2 : ℕ) ≤ n + 1 + 1 by omega), show n + 1 + 1 - 2 = n by omega,
      coeff_derivative, coeff_one, show (n + 1 + 1 : ℕ) ≠ 0 by omega, if_false, zero_add] at h
    simp only [pow_two, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i fSeries * coeff j fSeries)] at h
    simp only [fSeries, coeff_mk, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h ⊢
    have hsum : (∑ i ∈ range (n + 1), run i 1 * run (n - i) 1) =
        ∑ i ∈ range (n + 1), run i 1 * run (n + 1 - (i + 1)) 1 := by
      apply sum_congr rfl
      intro i _
      congr 2
      omega
    rw [hsum] at h
    linarith

private lemma a_eq_run (n : ℕ) : (a006014 (n + 1) : ℚ) = run n 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => norm_num [a006014, firstTable, run_zero]
    | succ n =>
      rw [a_recur, run_recur]
      push_cast
      rw [ih n (by omega)]
      congr 1
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      have hidx : n - i = (n - (i + 1)) + 1 := by omega
      rw [hidx, ih i (by omega), ih (n - (i + 1)) (by omega)]

end OMA.A006014

open OMA.A006014 OMA.S_oeis_a006014 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a006014.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have h := (a_eq_run m).trans (prefix_run m).symm
  simp only [prefixSum, dyad, pow_zero, one_mul] at h
  simpa [Nat.add_sub_cancel] using (show a006014 (m + 1) = ∑ k ∈ range (2 ^ m), a379818 k by exact_mod_cast h)
