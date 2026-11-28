import OMAStatements.S_oeis_a092468

-- Problem: A092468: a(n) = Sum_{i+j+k=n, 0<=i<=j<=k<=n} (n+2k)!/(i! * j! * (3*k)!).
-- Upstream: formal-conjectures statements/oeis-a092468.lean:0 (declaration OMA.S_oeis_a092468.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Disproof of Kotesovec's 2021 conjecture:
-- Because i <= j <= k and i + j + k = n force 3*k >= n, the multinomial bound on
-- (1 + 1 + 3)^(n + 2k) gives (a n)^3 <= (n + 1)^9 * (3125 / 27)^n, so the exponential
-- growth rate is at most (3125 / 27)^(1/3) = 5^(5/3) / 3 = 4.87336... < 4.874 < L = 4.87512...

namespace A092468Disproof

open Filter Topology Real

private lemma multinomial_three_bound (a b c : ℕ) :
    (((a + b + c).factorial : ℝ) /
      ((a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ))) * (3 : ℝ) ^ c ≤
      (5 : ℝ) ^ (a + b + c) := by
  have h1 : (a + b).choose a ≤ 2 ^ (a + b) := by
    rw [← Nat.sum_range_choose]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  have h2 : (a + b + c).choose c * 3 ^ c * 2 ^ (a + b) ≤ 5 ^ (a + b + c) := by
    have hadd := add_pow (3 : ℕ) 2 (a + b + c)
    rw [show (3 : ℕ) + 2 = 5 by norm_num] at hadd
    rw [hadd]
    have hmem : c ∈ Finset.range (a + b + c + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum
      (f := fun m => 3 ^ m * 2 ^ (a + b + c - m) * (a + b + c).choose m)
      (fun _ _ => Nat.zero_le _) hmem
    rw [show a + b + c - c = a + b by omega] at hle
    linarith
  have hfac1 : (a + b + c).choose c * c.factorial * (a + b).factorial = (a + b + c).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show c ≤ a + b + c by omega)
    rwa [show a + b + c - c = a + b by omega] at h
  have hfac2 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rwa [show a + b - a = b by omega] at h
  have hfac_nat : (a + b + c).factorial =
      (a + b + c).choose c * (a + b).choose a * (a.factorial * b.factorial * c.factorial) := by
    calc
      (a + b + c).factorial
          = (a + b + c).choose c * c.factorial * (a + b).factorial := hfac1.symm
      _ = (a + b + c).choose c * c.factorial * ((a + b).choose a * a.factorial * b.factorial) := by
            rw [hfac2]
      _ = (a + b + c).choose c * (a + b).choose a * (a.factorial * b.factorial * c.factorial) := by ring
  have hbound_nat : (a + b + c).choose c * (a + b).choose a * 3 ^ c ≤ 5 ^ (a + b + c) := by
    calc
      (a + b + c).choose c * (a + b).choose a * 3 ^ c
          = (a + b + c).choose c * 3 ^ c * (a + b).choose a := by ring
      _ ≤ (a + b + c).choose c * 3 ^ c * 2 ^ (a + b) := Nat.mul_le_mul_left _ h1
      _ ≤ 5 ^ (a + b + c) := h2
  have hden_ne : (a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ) ≠ 0 := by
    positivity
  have hfac_real : ((a + b + c).factorial : ℝ) =
      ((a + b + c).choose c : ℝ) * ((a + b).choose a : ℝ) *
        ((a.factorial : ℝ) * (b.factorial : ℝ) * (c.factorial : ℝ)) := by
    exact_mod_cast hfac_nat
  rw [hfac_real, mul_div_cancel_right₀ _ hden_ne]
  exact_mod_cast hbound_nat

private lemma term_cube_bound {n i j k : ℕ} (hsum : i + j + k = n) (hij : i ≤ j) (hjk : j ≤ k) :
    (((n + 2 * k).factorial : ℝ) /
      ((i.factorial : ℝ) * (j.factorial : ℝ) * ((3 * k).factorial : ℝ))) ^ 3 ≤
      (3125 / 27 : ℝ) ^ n := by
  have habc : i + j + 3 * k = n + 2 * k := by omega
  have hmb := multinomial_three_bound i j (3 * k)
  rw [habc] at hmb
  set T : ℝ := ((n + 2 * k).factorial : ℝ) /
    ((i.factorial : ℝ) * (j.factorial : ℝ) * ((3 * k).factorial : ℝ))
  have hT_nn : 0 ≤ T := by positivity
  have h3k : (3 : ℝ) ^ (3 * k) = (27 : ℝ) ^ k := by rw [pow_mul]; norm_num
  have h5k : (5 : ℝ) ^ (n + 2 * k) = (5 : ℝ) ^ n * (25 : ℝ) ^ k := by
    rw [pow_add, pow_mul]; norm_num
  rw [h3k, h5k] at hmb
  have hT_le : T ≤ (5 : ℝ) ^ n * (25 / 27 : ℝ) ^ k := by
    have h27 : (0 : ℝ) < (27 : ℝ) ^ k := by positivity
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ h27]
    exact hmb
  have hn_le_3k : n ≤ 3 * k := by omega
  have hpow_le : (25 / 27 : ℝ) ^ (3 * k) ≤ (25 / 27 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn_le_3k
  calc
    T ^ 3 ≤ ((5 : ℝ) ^ n * (25 / 27 : ℝ) ^ k) ^ 3 := pow_le_pow_left₀ hT_nn hT_le 3
    _ = (125 : ℝ) ^ n * (25 / 27 : ℝ) ^ (3 * k) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 3, pow_mul, mul_comm k 3]
          norm_num
    _ ≤ (125 : ℝ) ^ n * (25 / 27 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = (3125 / 27 : ℝ) ^ n := by rw [← mul_pow]; norm_num

private lemma a_ge_one (n : ℕ) : (1 : ℝ) ≤ (OMA.S_oeis_a092468.a n : ℝ) := by
  let S := (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = n ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)
  have hmem : (0, 0, n) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have ha_eq : (OMA.S_oeis_a092468.a n : ℝ) =
      ∑ t ∈ S, ((n + 2 * t.2.2).factorial : ℝ) /
        ((t.1.factorial : ℝ) * (t.2.1.factorial : ℝ) * ((3 * t.2.2).factorial : ℝ)) := by
    unfold OMA.S_oeis_a092468.a
    push_cast
    rfl
  rw [ha_eq]
  have hle := Finset.single_le_sum
    (f := fun t : ℕ × ℕ × ℕ => ((n + 2 * t.2.2).factorial : ℝ) /
      ((t.1.factorial : ℝ) * (t.2.1.factorial : ℝ) * ((3 * t.2.2).factorial : ℝ)))
    (fun _ _ => by positivity) hmem
  have h1 : ((n + 2 * n).factorial : ℝ) /
      (((0 : ℕ).factorial : ℝ) * ((0 : ℕ).factorial : ℝ) * ((3 * n).factorial : ℝ)) = 1 := by
    have hne : ((3 * n).factorial : ℝ) ≠ 0 := by positivity
    rw [show n + 2 * n = 3 * n by omega]
    simp [hne]
  linarith

private lemma a_cube_upper (n : ℕ) :
    (OMA.S_oeis_a092468.a n : ℝ) ^ 3 ≤ ((n + 1 : ℕ) : ℝ) ^ 9 * (3125 / 27 : ℝ) ^ n := by
  let S := (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = n ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)
  let f : ℕ × ℕ × ℕ → ℝ := fun t => ((n + 2 * t.2.2).factorial : ℝ) /
    ((t.1.factorial : ℝ) * (t.2.1.factorial : ℝ) * ((3 * t.2.2).factorial : ℝ))
  have ha_eq : (OMA.S_oeis_a092468.a n : ℝ) = ∑ t ∈ S, f t := by
    unfold OMA.S_oeis_a092468.a; push_cast; rfl
  have hSne : S.Nonempty := ⟨(0, 0, n), by
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega⟩
  obtain ⟨t₀, ht₀S, ht₀max⟩ := Finset.exists_max_image S f hSne
  have hScard : S.card ≤ (n + 1) ^ 3 := by
    have h1 : S.card ≤ (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simp only [Finset.card_product, Finset.card_range] at h1
    linarith [show (n + 1) * ((n + 1) * (n + 1)) = (n + 1) ^ 3 by ring]
  have ha_le : (OMA.S_oeis_a092468.a n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * f t₀ := by
    rw [ha_eq]
    calc
      ∑ t ∈ S, f t ≤ ∑ _t ∈ S, f t₀ := Finset.sum_le_sum fun t ht => ht₀max t ht
      _ = (S.card : ℝ) * f t₀ := by simp
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * f t₀ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) (by dsimp [f]; positivity)
  have ht₀_cond := (Finset.mem_filter.mp ht₀S).2
  have ht₀_cube : (f t₀) ^ 3 ≤ (3125 / 27 : ℝ) ^ n :=
    term_cube_bound ht₀_cond.1 ht₀_cond.2.1 ht₀_cond.2.2
  have ha_nn : 0 ≤ (OMA.S_oeis_a092468.a n : ℝ) := le_trans zero_le_one (a_ge_one n)
  calc
    (OMA.S_oeis_a092468.a n : ℝ) ^ 3
        ≤ (((n + 1 : ℕ) : ℝ) ^ 3 * f t₀) ^ 3 := pow_le_pow_left₀ ha_nn ha_le 3
    _ = ((n + 1 : ℕ) : ℝ) ^ 9 * (f t₀) ^ 3 := by ring
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ 9 * (3125 / 27 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left ht₀_cube (by positivity)

private lemma L_gt_rat : (4874 / 1000 : ℝ) < OMA.S_oeis_a092468.L := by
  unfold OMA.S_oeis_a092468.L
  set u : ℝ := (73 + 6 * √87) ^ (1 / 3 : ℝ)
  have hsqrt : (9327 / 1000 : ℝ) < √87 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hbase_nn : 0 ≤ 73 + 6 * √87 := by positivity
  have hu_nn : 0 ≤ u := Real.rpow_nonneg hbase_nn _
  have hu_cube : u ^ 3 = 73 + 6 * √87 := by
    rw [← Real.rpow_natCast u 3, ← Real.rpow_mul hbase_nn]
    norm_num
  have hu_gt : (5051 / 1000 : ℝ) < u := by
    by_contra hle
    push Not at hle
    have h1 : u ^ 3 ≤ (5051 / 1000 : ℝ) ^ 3 := pow_le_pow_left₀ hu_nn hle 3
    linarith [hu_cube, hsqrt, show (5051 / 1000 : ℝ) ^ 3 < 73 + 6 * (9327 / 1000 : ℝ) by norm_num]
  have hu_pos : 0 < u := by linarith
  have h3u_pos : 0 < 3 * u := by linarith
  have hquad : 0 < u ^ 2 - (7622 / 1000 : ℝ) * u + 13 := by
    nlinarith [sq_nonneg (u - 5051 / 1000)]
  have hdiff : (u / 3 + 13 / (3 * u) + 7 / 3) - 4874 / 1000 =
      (u ^ 2 - (7622 / 1000 : ℝ) * u + 13) / (3 * u) := by
    field_simp [ne_of_gt hu_pos]
    ring
  have hpos_diff : 0 < (u ^ 2 - (7622 / 1000 : ℝ) * u + 13) / (3 * u) :=
    div_pos hquad h3u_pos
  linarith

end A092468Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a092468.main) := by
  intro hlim
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      (4874 / 1000 : ℝ) < (OMA.S_oeis_a092468.a (n + 1) : ℝ) / (OMA.S_oeis_a092468.a n : ℝ) :=
    hlim.eventually (Ioi_mem_nhds A092468Disproof.L_gt_rat)
  rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
  have hgrow : ∀ m : ℕ, (4874 / 1000 : ℝ) ^ m * (OMA.S_oeis_a092468.a N : ℝ) ≤
      (OMA.S_oeis_a092468.a (N + m) : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hpos : (0 : ℝ) < (OMA.S_oeis_a092468.a (N + m) : ℝ) :=
        lt_of_lt_of_le zero_lt_one (A092468Disproof.a_ge_one (N + m))
      have hstep := hN (N + m) (by omega)
      rw [lt_div_iff₀ hpos] at hstep
      have h1 : (4874 / 1000 : ℝ) * ((4874 / 1000 : ℝ) ^ m * (OMA.S_oeis_a092468.a N : ℝ)) ≤
          (4874 / 1000 : ℝ) * (OMA.S_oeis_a092468.a (N + m) : ℝ) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      rw [show N + (m + 1) = N + m + 1 by omega, pow_succ']
      linarith
  set r : ℝ := (4874 / 1000 : ℝ) ^ 3
  set q : ℝ := (3125 / 27 : ℝ) / r
  have hr_pos : 0 < r := by positivity
  have hq_nn : 0 ≤ q := by positivity
  have hq_lt : q < 1 := by
    dsimp only [q, r]
    norm_num
  have hq_norm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq_nn]
    exact hq_lt
  have hzero : Filter.Tendsto (fun m : ℕ =>
      (3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9 * ((m : ℝ) ^ 9 * q ^ m))
      Filter.atTop (nhds 0) := by
    have hsum := summable_pow_mul_geometric_of_norm_lt_one 9 hq_norm
    simpa using hsum.tendsto_atTop_zero.const_mul ((3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9)
  have hle_ev : ∀ᶠ m : ℕ in Filter.atTop,
      (1 : ℝ) ≤ (3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9 * ((m : ℝ) ^ 9 * q ^ m) := by
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with m hm
    have h1 := hgrow m
    have haN : (1 : ℝ) ≤ (OMA.S_oeis_a092468.a N : ℝ) := A092468Disproof.a_ge_one N
    have hcube1 : r ^ m ≤ (OMA.S_oeis_a092468.a (N + m) : ℝ) ^ 3 := by
      have h1' : (4874 / 1000 : ℝ) ^ m ≤ (OMA.S_oeis_a092468.a (N + m) : ℝ) := by
        have := mul_le_mul_of_nonneg_left haN (show (0 : ℝ) ≤ (4874 / 1000 : ℝ) ^ m by positivity)
        linarith
      have hc := pow_le_pow_left₀ (by positivity) h1' 3
      rw [← pow_mul, mul_comm m 3, pow_mul] at hc
      exact hc
    have hcube2 := A092468Disproof.a_cube_upper (N + m)
    have hnm_le : ((N + m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
      have : N + m + 1 ≤ 2 * m := by omega
      exact_mod_cast this
    have hnm9 : ((N + m + 1 : ℕ) : ℝ) ^ 9 ≤ (2 : ℝ) ^ 9 * (m : ℝ) ^ 9 := by
      calc ((N + m + 1 : ℕ) : ℝ) ^ 9 ≤ (2 * (m : ℝ)) ^ 9 := pow_le_pow_left₀ (by positivity) hnm_le 9
        _ = (2 : ℝ) ^ 9 * (m : ℝ) ^ 9 := mul_pow _ _ _
    have hcomb : r ^ m ≤ (3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9 * (m : ℝ) ^ 9 * (3125 / 27 : ℝ) ^ m := by
      have htrans := le_trans hcube1 hcube2
      rw [pow_add] at htrans
      have h2 := mul_le_mul_of_nonneg_right hnm9 (show (0 : ℝ) ≤ (3125 / 27 : ℝ) ^ N * (3125 / 27 : ℝ) ^ m by positivity)
      linarith [show ((2 : ℝ) ^ 9 * (m : ℝ) ^ 9) * ((3125 / 27 : ℝ) ^ N * (3125 / 27 : ℝ) ^ m) =
        (3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9 * (m : ℝ) ^ 9 * (3125 / 27 : ℝ) ^ m by ring]
    have hdiv := div_le_div_of_nonneg_right hcomb (show (0 : ℝ) ≤ r ^ m by positivity)
    rw [div_self (ne_of_gt (pow_pos hr_pos m))] at hdiv
    have hrew : (3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9 * (m : ℝ) ^ 9 * (3125 / 27 : ℝ) ^ m / r ^ m =
        (3125 / 27 : ℝ) ^ N * (2 : ℝ) ^ 9 * ((m : ℝ) ^ 9 * q ^ m) := by
      dsimp only [q]
      rw [div_pow]
      ring
    rwa [hrew] at hdiv
  have hcontra : (1 : ℝ) ≤ 0 := ge_of_tendsto hzero hle_ev
  norm_num at hcontra
