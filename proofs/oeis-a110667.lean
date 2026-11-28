import OMAStatements.S_oeis_a110667

-- Problem: A110667: Sequence is {a(2,n)}, where a(m,n) is defined at sequence A110665.
-- Upstream: formal-conjectures statements/oeis-a110667.lean:0 (declaration OMA.S_oeis_a110667.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a110667
open PowerSeries

private def invOneSub : PowerSeries ℤ := mk (fun _ => 1)

private lemma one_sub_X_mul_invOneSub : (1 - X) * invOneSub = 1 := by
  ext n
  cases n with
  | zero => simp [invOneSub]
  | succ n => simp [invOneSub, sub_mul]

private lemma coeff_invOneSub_pow (k m : ℕ) (hk : 1 ≤ k) :
    coeff m (invOneSub ^ k) = (Nat.choose (m + k - 1) (k - 1) : ℤ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  induction k generalizing m with
  | zero => simp [invOneSub]
  | succ k ih =>
    rw [pow_succ, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (invOneSub ^ (k + 1)) * coeff j invOneSub)]
    simp only [invOneSub, coeff_mk, mul_one]
    have hsum : (∑ i ∈ Finset.range (m + 1), coeff i ((mk fun _ => 1) ^ (k + 1))) =
        ∑ i ∈ Finset.range (m + 1), (Nat.choose (i + k) k : ℤ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa [invOneSub] using ih i
    rw [hsum]
    clear hsum ih
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [Finset.sum_range_succ, ihm]
      rw [show m + 1 + (k + 1 + 1) - 1 = (m + k + 1) + 1 by omega,
        show m + (k + 1 + 1) - 1 = m + k + 1 by omega,
        show k + 1 + 1 - 1 = k + 1 by omega,
        show m + 1 + k = m + k + 1 by omega]
      rw [Nat.choose_succ_succ (m + k + 1) k]
      push_cast
      ring

private noncomputable def W : PowerSeries ℤ := X * (1 - X)

private noncomputable def P (N : ℕ) : PowerSeries ℤ :=
  ∑ m ∈ Finset.range N, ((m + 1 : ℤ) : PowerSeries ℤ) * W ^ m

private noncomputable def g (n : ℕ) : ℤ :=
  coeff n (X * (1 - 2 * X) * P (n + 1))

private lemma g_zero : g 0 = 0 := by
  simp [g, mul_assoc]

private lemma coeff_X_mul_W_pow_eq_zero {N k : ℕ} (hk : k ≤ N) (f : PowerSeries ℤ) :
    coeff k (X * f * W ^ N) = 0 := by
  have hW : X ^ N ∣ W ^ N := pow_dvd_pow_of_dvd ⟨1 - X, rfl⟩ N
  obtain ⟨q, hq⟩ := hW
  have hdiv : X ^ (N + 1) ∣ X * f * W ^ N := by
    refine ⟨f * q, ?_⟩
    rw [hq, pow_succ']
    ring
  obtain ⟨q', hq'⟩ := hdiv
  rw [hq', coeff_X_pow_mul' q' (N + 1) k, if_neg (by omega)]

private lemma g_eq_coeff_P {N k : ℕ} (hk : k ≤ N) :
    g k = coeff k (X * (1 - 2 * X) * P N) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero =>
    simp only [add_zero, g, P, Finset.sum_range_succ, mul_add, map_add]
    have h0 : coeff k (X * (1 - 2 * X) * (((k + 1 : ℤ) : PowerSeries ℤ) * W ^ k)) = 0 := by
      have := coeff_X_mul_W_pow_eq_zero (le_refl k) ((1 - 2 * X) * ((k + 1 : ℤ) : PowerSeries ℤ))
      simpa [mul_assoc] using this
    rw [h0, add_zero]
  | succ d ih =>
    rw [ih (by omega), show k + (d + 1) = (k + d) + 1 by omega]
    simp only [P, Finset.sum_range_succ, mul_add, map_add]
    have h0 : coeff k (X * (1 - 2 * X) * ((((k + d : ℕ) + 1 : ℤ) : PowerSeries ℤ) * W ^ (k + d))) = 0 := by
      have := coeff_X_mul_W_pow_eq_zero (by omega : k ≤ k + d)
        ((1 - 2 * X) * ((((k + d : ℕ) + 1 : ℤ) : PowerSeries ℤ)))
      simpa [mul_assoc] using this
    rw [h0, add_zero]

private lemma gf_g : (X ^ 2 - X + 1) ^ 2 * PowerSeries.mk g = X * (1 - 2 * X) := by
  ext n
  have h1W : 1 - W = X ^ 2 - X + 1 := by
    rw [W]; ring
  have hP_id : (1 - W) ^ 2 * P (n + 1) =
      1 - W ^ (n + 1) * (1 + ((n + 1 : ℤ) : PowerSeries ℤ) * (1 - W)) := by
    have h1 : (1 - W) * P (n + 1) =
        (∑ m ∈ Finset.range (n + 1), W ^ m) - ((n + 1 : ℤ) : PowerSeries ℤ) * W ^ (n + 1) := by
      clear h1W
      induction n with
      | zero => simp [P]
      | succ n ih =>
        rw [P, Finset.sum_range_succ, mul_add, ← P, ih]
        rw [show n + 1 + 1 = (n + 1) + 1 from rfl, Finset.sum_range_succ _ (n + 1)]
        push_cast
        ring
    have h2 : (1 - W) * (∑ m ∈ Finset.range (n + 1), W ^ m) = 1 - W ^ (n + 1) := by
      rw [← neg_sub W 1, neg_mul, mul_comm, geom_sum_mul, neg_sub]
    calc (1 - W) ^ 2 * P (n + 1)
        = (1 - W) * ((1 - W) * P (n + 1)) := by ring
      _ = (1 - W) * (∑ m ∈ Finset.range (n + 1), W ^ m) -
            ((n + 1 : ℤ) : PowerSeries ℤ) * (1 - W) * W ^ (n + 1) := by
          rw [h1]; ring
      _ = 1 - W ^ (n + 1) * (1 + ((n + 1 : ℤ) : PowerSeries ℤ) * (1 - W)) := by
          rw [h2]; ring
  have hmk : coeff n ((X ^ 2 - X + 1) ^ 2 * PowerSeries.mk g) =
      coeff n ((X ^ 2 - X + 1) ^ 2 * (X * (1 - 2 * X) * P (n + 1))) := by
    rw [coeff_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i ((X ^ 2 - X + 1) ^ 2) * coeff j (PowerSeries.mk g)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i ((X ^ 2 - X + 1) ^ 2) * coeff j (X * (1 - 2 * X) * P (n + 1)))]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi_le : n - i ≤ n + 1 := by omega
    rw [coeff_mk, g_eq_coeff_P hi_le]
  rw [hmk, ← h1W, mul_left_comm, hP_id, mul_sub, mul_one, map_sub]
  have h0 : coeff n (X * (1 - 2 * X) * (W ^ (n + 1) * (1 + ((n + 1 : ℤ) : PowerSeries ℤ) * (1 - W)))) = 0 := by
    have := coeff_X_mul_W_pow_eq_zero (Nat.le_succ n)
      ((1 - 2 * X) * (1 + ((n + 1 : ℤ) : PowerSeries ℤ) * (1 - W)))
    simpa [mul_assoc, mul_comm (W ^ (n + 1))] using this
  rw [h0, sub_zero]

private lemma choose_two_mul_eq (k : ℕ) (hk : 1 ≤ k) :
    Nat.choose (2 * k) k = 2 * Nat.choose (2 * k - 1) (k - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Nat.choose_succ_succ,
    show 2 * k + 1 + 1 - 1 = 2 * k + 1 by omega, Nat.add_sub_cancel]
  have hsymm : Nat.choose (2 * k + 1) (k + 1) = Nat.choose (2 * k + 1) k := by
    rw [← Nat.choose_symm (by omega : k + 1 ≤ 2 * k + 1)]
    congr 1
    omega
  rw [hsymm]
  omega

private lemma sum_choose_mul_g (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (Nat.choose (2 * n - k - 1) (n - 1) : ℤ) * g k = n := by
  have hsum_eq : ∑ k ∈ Finset.Icc 1 n, (Nat.choose (2 * n - k - 1) (n - 1) : ℤ) * g k =
      coeff n (invOneSub ^ n * (X * (1 - 2 * X) * P n)) := by
    rw [mul_comm (invOneSub ^ n), coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (X * (1 - 2 * X) * P n) * coeff j (invOneSub ^ n))]
    have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
    have h0' : coeff 0 (X * (1 - 2 * X) * P n) * coeff (n - 0) (invOneSub ^ n) = 0 := by
      simp [mul_assoc]
    rw [h0', zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    rw [coeff_invOneSub_pow n (n - k) hn, ← g_eq_coeff_P hk.2, mul_comm]
    rw [show 2 * n - k - 1 = n - k + n - 1 by omega]
  rw [hsum_eq, P, Finset.mul_sum, Finset.mul_sum, map_sum]
  have hterm : ∀ m ∈ Finset.range n,
      coeff n (invOneSub ^ n * (X * (1 - 2 * X) * (((m + 1 : ℤ) : PowerSeries ℤ) * W ^ m))) =
        if m + 1 = n then (n : ℤ) else 0 := by
    intro m hm
    rw [Finset.mem_range] at hm
    have hpow_sub : invOneSub ^ n * (1 - X) ^ m = invOneSub ^ (n - m) := by
      nth_rw 1 [← Nat.sub_add_cancel hm.le]
      rw [pow_add, mul_assoc, ← mul_pow,
        mul_comm invOneSub (1 - X), one_sub_X_mul_invOneSub, one_pow, mul_one]
    have hrewrite : invOneSub ^ n * (X * (1 - 2 * X) * (((m + 1 : ℤ) : PowerSeries ℤ) * W ^ m)) =
        ((m + 1 : ℤ) : PowerSeries ℤ) * (X ^ (m + 1) * ((1 - 2 * X) * invOneSub ^ (n - m))) := by
      rw [W, mul_pow, pow_succ]
      calc invOneSub ^ n * (X * (1 - 2 * X) * (((m + 1 : ℤ) : PowerSeries ℤ) * (X ^ m * (1 - X) ^ m)))
          = ((m + 1 : ℤ) : PowerSeries ℤ) * ((X ^ m * X) * ((1 - 2 * X) * (invOneSub ^ n * (1 - X) ^ m))) := by
              ring
        _ = ((m + 1 : ℤ) : PowerSeries ℤ) * ((X ^ m * X) * ((1 - 2 * X) * invOneSub ^ (n - m))) := by
              rw [hpow_sub]
    rw [hrewrite]
    have hcoeff_m : ∀ f : PowerSeries ℤ,
        coeff n (((m + 1 : ℤ) : PowerSeries ℤ) * (X ^ (m + 1) * f)) =
          (m + 1 : ℤ) * coeff (n - (m + 1)) f := by
      intro f
      have hcast : ((m + 1 : ℤ) : PowerSeries ℤ) * (X ^ (m + 1) * f) =
          ((m : ℤ) + 1) • (X ^ (m + 1) * f) := by simp [zsmul_eq_mul]
      rw [hcast, map_zsmul, coeff_X_pow_mul' f (m + 1) n, if_pos (by omega), smul_eq_mul]
    rw [hcoeff_m]
    set k := n - (m + 1)
    have hnm : n - m = k + 1 := by omega
    rw [hnm]
    by_cases hk0 : k = 0
    · have hm_eq : m + 1 = n := by omega
      simp only [hk0, hm_eq, Nat.zero_add, pow_one, invOneSub]
      norm_num
      omega
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have hm_ne : m + 1 ≠ n := by omega
      rw [if_neg hm_ne]
      have hdiff : coeff k ((1 - 2 * X) * invOneSub ^ (k + 1)) = 0 := by
        rw [sub_mul, one_mul, map_sub, coeff_invOneSub_pow (k + 1) k (by omega)]
        have h2X : coeff k (2 * X * invOneSub ^ (k + 1)) =
            2 * coeff (k - 1) (invOneSub ^ (k + 1)) := by
          rw [mul_assoc, show (2 : PowerSeries ℤ) * (X * invOneSub ^ (k + 1)) =
            (2 : ℤ) • (X * invOneSub ^ (k + 1)) by simp, map_zsmul]
          congr 1
          rw [← pow_one X, coeff_X_pow_mul' (invOneSub ^ (k + 1)) 1 k, if_pos hk1]
        rw [h2X, coeff_invOneSub_pow (k + 1) (k - 1) (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [show k + (k + 1) - 1 = 2 * k by omega,
          show k - 1 + (k + 1) - 1 = 2 * k - 1 by omega]
        have hsymm : Nat.choose (2 * k - 1) k = Nat.choose (2 * k - 1) (k - 1) := by
          rw [← Nat.choose_symm (by omega : k ≤ 2 * k - 1)]
          congr 1; omega
        rw [hsymm, choose_two_mul_eq k hk1]
        push_cast
        ring
      rw [hdiff, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single (n - 1)]
  · simp [show n - 1 + 1 = n by omega]
  · intro m hm hne
    rw [Finset.mem_range] at hm
    rw [if_neg (by omega)]
  · intro h
    exfalso
    exact h (Finset.mem_range.mpr (by omega))

private lemma row0_zero : row0 0 = 0 := by
  rw [row0]
  simp

private lemma row0_eq_g (n : ℕ) : row0 n = g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [g_zero, row0_zero]
    | succ n =>
      rw [row0]
      have hih : ∑ k : Fin (n + 1), ((Nat.choose (2 * (n + 1) - k - 1) n : ℕ) : ℤ) * row0 k =
          ∑ k : Fin (n + 1), ((Nat.choose (2 * (n + 1) - k - 1) n : ℕ) : ℤ) * g k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ih k k.2]
      simp only [Nat.succ_sub_one] at hih ⊢
      rw [hih, Fin.sum_univ_eq_sum_range (fun k => ((Nat.choose (2 * (n + 1) - k - 1) n : ℕ) : ℤ) * g k)]
      have hsum := sum_choose_mul_g (n + 1) (Nat.succ_pos n)
      simp only [Nat.succ_sub_one] at hsum
      have hsplit : ∑ k ∈ Finset.Icc 1 (n + 1), (Nat.choose (2 * (n + 1) - k - 1) n : ℤ) * g k =
          (∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * (n + 1) - k - 1) n : ℤ) * g k) + g (n + 1) := by
        have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Ico 1 (n + 1)) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
        rw [hIcc, Finset.sum_insert (by simp)]
        have hself : Nat.choose (2 * (n + 1) - (n + 1) - 1) n = 1 := by
          rw [show 2 * (n + 1) - (n + 1) - 1 = n by omega, Nat.choose_self]
        rw [hself, Nat.cast_one, one_mul, add_comm]
        congr 1
        have h0 : (Nat.choose (2 * (n + 1) - 0 - 1) n : ℤ) * g 0 = 0 := by rw [g_zero, mul_zero]
        have hrange : Finset.range (n + 1) = insert 0 (Finset.Ico 1 (n + 1)) := by
          ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
        rw [hrange, Finset.sum_insert (by simp), h0, zero_add]
      linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a110667.main := by
  have hrow0 : PowerSeries.mk row0 = PowerSeries.mk g := by
    ext n
    simp [row0_eq_g n]
  have hgf0 : (X ^ 2 - X + 1) ^ 2 * PowerSeries.mk row0 = X * (1 - 2 * X) := by
    rw [hrow0, gf_g]
  have hrow1 : (1 - X) * PowerSeries.mk row1 = PowerSeries.mk row0 := by
    ext n
    cases n with
    | zero =>
      simp [row1, row0_zero]
    | succ n =>
      rw [sub_mul, one_mul, map_sub, coeff_mk, coeff_mk]
      have hX : coeff (n + 1) (X * PowerSeries.mk row1) = row1 n := by
        rw [← pow_one X, coeff_X_pow_mul' (PowerSeries.mk row1) 1 (n + 1), if_pos (by omega), coeff_mk]
        simp
      rw [hX, row1]
      ring
  have hrow2 : (1 - X) * PowerSeries.mk a = PowerSeries.mk row1 := by
    ext n
    cases n with
    | zero =>
      simp [a, row1]
    | succ n =>
      rw [sub_mul, one_mul, map_sub, coeff_mk, coeff_mk]
      have hX : coeff (n + 1) (X * PowerSeries.mk a) = a n := by
        rw [← pow_one X, coeff_X_pow_mul' (PowerSeries.mk a) 1 (n + 1), if_pos (by omega), coeff_mk]
        simp
      rw [hX, a]
      ring
  calc (X - 1) ^ 2 * (X ^ 2 - X + 1) ^ 2 * PowerSeries.mk a
      = (X ^ 2 - X + 1) ^ 2 * ((1 - X) * ((1 - X) * PowerSeries.mk a)) := by ring
    _ = (X ^ 2 - X + 1) ^ 2 * PowerSeries.mk row0 := by rw [hrow2, hrow1]
    _ = X * (1 - 2 * X) := hgf0
    _ = -X * (-1 + 2 * X) := by ring
