import OMAStatements.S_mo_128291

namespace OMA.mo_128291_proof

private lemma sum_choose_mul_pow (r : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (r + 1), (r.choose t : ℚ) * x ^ t = (1 + x) ^ r := by
  have h := add_pow x 1 r
  simp only [one_pow, mul_one] at h
  rw [add_comm 1 x, h]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

private lemma sum_mul_choose_mul_pow (r : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (r + 1), (t : ℚ) * (r.choose t : ℚ) * x ^ t =
      (r : ℚ) * x * (1 + x) ^ (r - 1) := by
  cases r with
  | zero => simp
  | succ r' =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.succ_sub_succ_eq_sub, tsub_zero]
    have hstep : ∀ t ∈ Finset.range (r' + 1),
        ((t + 1 : ℕ) : ℚ) * ((r' + 1).choose (t + 1) : ℚ) * x ^ (t + 1) =
          ((r' + 1 : ℕ) : ℚ) * x * ((r'.choose t : ℚ) * x ^ t) := by
      intro t _
      have hchoose : (t + 1) * (r' + 1).choose (t + 1) = (r' + 1) * r'.choose t := by
        rw [mul_comm, ← Nat.add_one_mul_choose_eq]
      have hq : ((t + 1 : ℕ) : ℚ) * ((r' + 1).choose (t + 1) : ℚ) =
          ((r' + 1 : ℕ) : ℚ) * (r'.choose t : ℚ) := by
        exact_mod_cast hchoose
      calc
        ((t + 1 : ℕ) : ℚ) * ((r' + 1).choose (t + 1) : ℚ) * x ^ (t + 1)
            = (((r' + 1 : ℕ) : ℚ) * (r'.choose t : ℚ)) * (x * x ^ t) := by
              rw [hq, pow_succ']
        _ = ((r' + 1 : ℕ) : ℚ) * x * ((r'.choose t : ℚ) * x ^ t) := by ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_choose_mul_pow]

private lemma sum_mul_pred_choose_mul_pow (r : ℕ) (x : ℚ) :
    ∑ t ∈ Finset.range (r + 1), (t : ℚ) * ((t : ℚ) - 1) * (r.choose t : ℚ) * x ^ t =
      (r : ℚ) * ((r : ℚ) - 1) * x ^ 2 * (1 + x) ^ (r - 2) := by
  rcases r with _ | _ | r'
  · simp
  · simp [Finset.sum_range_succ]
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [Finset.sum_range_succ']
    simp only [Nat.zero_add, Nat.cast_one, sub_self, mul_zero, zero_mul, add_zero]
    have hstep : ∀ t ∈ Finset.range (r' + 1),
        ((t + 1 + 1 : ℕ) : ℚ) * (((t + 1 + 1 : ℕ) : ℚ) - 1) *
            ((r' + 2).choose (t + 1 + 1) : ℚ) * x ^ (t + 1 + 1) =
          ((r' + 2 : ℕ) : ℚ) * (((r' + 2 : ℕ) : ℚ) - 1) * x ^ 2 *
            ((r'.choose t : ℚ) * x ^ t) := by
      intro t _
      have h1 : (t + 2) * (r' + 2).choose (t + 2) = (r' + 2) * (r' + 1).choose (t + 1) := by
        rw [mul_comm, ← Nat.add_one_mul_choose_eq]
      have h2 : (t + 1) * (r' + 1).choose (t + 1) = (r' + 1) * r'.choose t := by
        rw [mul_comm, ← Nat.add_one_mul_choose_eq]
      have hchoose : (t + 2) * (t + 1) * (r' + 2).choose (t + 2) =
          (r' + 2) * (r' + 1) * r'.choose t := by
        calc
          (t + 2) * (t + 1) * (r' + 2).choose (t + 2)
              = (t + 1) * ((t + 2) * (r' + 2).choose (t + 2)) := by ring
          _ = (r' + 2) * ((t + 1) * (r' + 1).choose (t + 1)) := by rw [h1]; ring
          _ = (r' + 2) * (r' + 1) * r'.choose t := by rw [h2]; ring
      have hq : ((t + 2 : ℕ) : ℚ) * ((t + 1 : ℕ) : ℚ) * ((r' + 2).choose (t + 2) : ℚ) =
          ((r' + 2 : ℕ) : ℚ) * ((r' + 1 : ℕ) : ℚ) * (r'.choose t : ℚ) := by
        exact_mod_cast hchoose
      have ht1 : (((t + 1 + 1 : ℕ) : ℚ) - 1) = ((t + 1 : ℕ) : ℚ) := by push_cast; ring
      have hr1 : (((r' + 2 : ℕ) : ℚ) - 1) = ((r' + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [ht1, hr1]
      have hpow : x ^ (t + 1 + 1) = x ^ 2 * x ^ t := by ring
      rw [show t + 1 + 1 = t + 2 by rfl, hpow]
      calc
        ((t + 2 : ℕ) : ℚ) * ((t + 1 : ℕ) : ℚ) * ((r' + 2).choose (t + 2) : ℚ) * (x ^ 2 * x ^ t)
            = (((t + 2 : ℕ) : ℚ) * ((t + 1 : ℕ) : ℚ) * ((r' + 2).choose (t + 2) : ℚ)) *
                (x ^ 2 * x ^ t) := by ring
        _ = (((r' + 2 : ℕ) : ℚ) * ((r' + 1 : ℕ) : ℚ) * (r'.choose t : ℚ)) *
              (x ^ 2 * x ^ t) := by rw [hq]
        _ = ((r' + 2 : ℕ) : ℚ) * ((r' + 1 : ℕ) : ℚ) * x ^ 2 * ((r'.choose t : ℚ) * x ^ t) := by
              ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, sum_choose_mul_pow]
    rw [show r' + 1 + 1 - 2 = r' from rfl]

private lemma quad_choose_sum (n j m r : ℕ) (hn : (n : ℚ) ≠ 0) (hjr : j + r = n) (hr : 1 ≤ r) :
    ∑ t ∈ Finset.range (r + 1),
        (((j : ℚ) + t + m) * ((j : ℚ) + t) * (r.choose t : ℚ) * (-(j : ℚ) / n) ^ t) =
      -(j : ℚ) * ((r : ℚ) / n) ^ (r - 1) := by
  have hpoly : ∀ t ∈ Finset.range (r + 1),
      ((j : ℚ) + t + m) * ((j : ℚ) + t) * (r.choose t : ℚ) * (-(j : ℚ) / n) ^ t =
        ((j : ℚ) * ((j : ℚ) + m)) * ((r.choose t : ℚ) * (-(j : ℚ) / n) ^ t) +
        (2 * (j : ℚ) + m + 1) * ((t : ℚ) * (r.choose t : ℚ) * (-(j : ℚ) / n) ^ t) +
        ((t : ℚ) * ((t : ℚ) - 1) * (r.choose t : ℚ) * (-(j : ℚ) / n) ^ t) := by
    intro t _
    ring
  rw [Finset.sum_congr rfl hpoly, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    sum_choose_mul_pow, sum_mul_choose_mul_pow, sum_mul_pred_choose_mul_pow]
  have h1x : (1 : ℚ) + -(j : ℚ) / n = (r : ℚ) / n := by
    have hq : (j : ℚ) + r = n := by exact_mod_cast hjr
    field_simp
    linarith
  rw [h1x]
  rcases r with _ | _ | r'
  · omega
  · have hnq : (n : ℚ) = (j : ℚ) + 1 := by exact_mod_cast hjr.symm
    have hj1_ne : (j : ℚ) + 1 ≠ 0 := by positivity
    norm_num
    rw [hnq]
    field_simp
    ring
  · have hcast : ((r' + 2 : ℕ) : ℚ) = (r' : ℚ) + 2 := by push_cast; ring
    have hnq : (n : ℚ) = (j : ℚ) + (r' : ℚ) + 2 := by
      have hq : (j : ℚ) + (r' + 2) = n := by exact_mod_cast hjr
      linarith
    simp only [Nat.add_sub_cancel]
    rw [show (((r' + 2 : ℕ) : ℚ) / n) ^ (r' + 2) =
          (((r' + 2 : ℕ) : ℚ) / n) ^ 2 * (((r' + 2 : ℕ) : ℚ) / n) ^ r' by ring]
    nth_rw 1 [show (((r' + 2 : ℕ) : ℚ) / n) ^ (r' + 1) =
          (((r' + 2 : ℕ) : ℚ) / n) * (((r' + 2 : ℕ) : ℚ) / n) ^ r' by ring]
    have hcoeff :
        ((j : ℚ) * ((j : ℚ) + m)) * (((r' + 2 : ℕ) : ℚ) / n) ^ 2 +
          (2 * (j : ℚ) + m + 1) * (((r' + 2 : ℕ) : ℚ) * (-(j : ℚ) / n) * (((r' + 2 : ℕ) : ℚ) / n)) +
          ((r' + 2 : ℕ) : ℚ) * (((r' + 2 : ℕ) : ℚ) - 1) * (-(j : ℚ) / n) ^ 2 =
        -(j : ℚ) * (((r' + 2 : ℕ) : ℚ) / n) := by
      rw [hcast]
      field_simp
      rw [hnq]
      ring
    calc
      ((j : ℚ) * ((j : ℚ) + m)) * ((((r' + 2 : ℕ) : ℚ) / n) ^ 2 * (((r' + 2 : ℕ) : ℚ) / n) ^ r') +
          (2 * (j : ℚ) + m + 1) * (((r' + 2 : ℕ) : ℚ) * (-(j : ℚ) / n) * ((((r' + 2 : ℕ) : ℚ) / n) * (((r' + 2 : ℕ) : ℚ) / n) ^ r')) +
          ((r' + 2 : ℕ) : ℚ) * (((r' + 2 : ℕ) : ℚ) - 1) * (-(j : ℚ) / n) ^ 2 * (((r' + 2 : ℕ) : ℚ) / n) ^ r'
          = (((j : ℚ) * ((j : ℚ) + m)) * (((r' + 2 : ℕ) : ℚ) / n) ^ 2 +
              (2 * (j : ℚ) + m + 1) * (((r' + 2 : ℕ) : ℚ) * (-(j : ℚ) / n) * (((r' + 2 : ℕ) : ℚ) / n)) +
              ((r' + 2 : ℕ) : ℚ) * (((r' + 2 : ℕ) : ℚ) - 1) * (-(j : ℚ) / n) ^ 2) *
              (((r' + 2 : ℕ) : ℚ) / n) ^ r' := by ring
      _ = -(j : ℚ) * (((r' + 2 : ℕ) : ℚ) / n) * (((r' + 2 : ℕ) : ℚ) / n) ^ r' := by rw [hcoeff]
      _ = -(j : ℚ) * (((r' + 2 : ℕ) : ℚ) / n) ^ (r' + 1) := by rw [pow_succ']; ring

end OMA.mo_128291_proof

theorem OMA.solution : type_of% @OMA.S_mo_128291.main := by
  intro n m hn hm
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm0 : m ≠ 0 := by omega
  let F : ℕ → ℕ → ℚ := fun s j =>
    ((s : ℚ) + m) * (n.choose s : ℚ) *
      ((-1 : ℚ) ^ (s - j) * (s.choose j : ℚ) * ((j : ℚ) / n) ^ (s + m - 1)) * (s : ℚ) / n
  -- Step 1: reindex inner sum via j = s - i and drop j = 0
  have hlhs1 :
      (∑ s ∈ Finset.Icc 1 n, ((s : ℚ) + m) * (n.choose s : ℚ) *
        (∑ i ∈ Finset.range (s + 1), (-1 : ℚ) ^ i * (s.choose i : ℚ) *
          (((s - i : ℕ) : ℚ) / n) ^ (s + m - 1)) * (s : ℚ) / n) =
      ∑ s ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 s, F s j := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    let g : ℕ → ℚ := fun j => (-1 : ℚ) ^ (s - j) * (s.choose j : ℚ) * ((j : ℚ) / n) ^ (s + m - 1)
    have h1 :
        (∑ i ∈ Finset.range (s + 1), (-1 : ℚ) ^ i * (s.choose i : ℚ) *
          (((s - i : ℕ) : ℚ) / n) ^ (s + m - 1)) =
        ∑ i ∈ Finset.range (s + 1), g (s + 1 - 1 - i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have his : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsub1 : s + 1 - 1 - i = s - i := by omega
      dsimp only [g]
      rw [hsub1, Nat.sub_sub_self his, Nat.choose_symm his]
    have h2 : ∑ i ∈ Finset.range (s + 1), g (s + 1 - 1 - i) = ∑ j ∈ Finset.range (s + 1), g j :=
      Finset.sum_range_reflect g (s + 1)
    have h3 : ∑ j ∈ Finset.range (s + 1), g j = ∑ j ∈ Finset.Icc 1 s, g j := by
      rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ s)]
      have hg0 : g 0 = 0 := by
        dsimp only [g]
        simp [zero_pow (by omega : s + m - 1 ≠ 0)]
      rw [hg0, zero_add]
      have hIco : Finset.Ico 1 (s + 1) = Finset.Icc 1 s := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [hIco]
    rw [h1, h2, h3, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  -- Step 2: swap the two sums
  have hlhs2 :
      (∑ s ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 s, F s j) =
      ∑ j ∈ Finset.Icc 1 n, ∑ s ∈ Finset.Icc j n, F s j := by
    have hite : ∀ s ∈ Finset.Icc 1 n,
        ∑ j ∈ Finset.Icc 1 s, F s j = ∑ j ∈ Finset.Icc 1 n, if j ≤ s then F s j else 0 := by
      intro s hs
      rw [← Finset.sum_filter]
      congr 1
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc]
      have hsn : s ≤ n := (Finset.mem_Icc.mp hs).2
      omega
    rw [Finset.sum_congr rfl hite, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  -- Step 3: reindex s = j + t and evaluate inner sum for each j
  have hlhs3 : ∀ j ∈ Finset.Icc 1 n,
      (∑ s ∈ Finset.Icc j n, F s j) =
      (n.choose j : ℚ) * ((j : ℚ) / n) ^ (j + m - 1) / n *
        ∑ t ∈ Finset.range (n - j + 1),
          ((j : ℚ) + t + m) * ((j : ℚ) + t) * ((n - j).choose t : ℚ) * (-(j : ℚ) / n) ^ t := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hbij :
        ∑ s ∈ Finset.Icc j n, F s j =
        ∑ t ∈ Finset.range (n - j + 1), F (j + t) j := by
      symm
      refine Finset.sum_bij (fun t _ => j + t) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_range] at ht
        simp only [Finset.mem_Icc]
        omega
      · intro t1 _ t2 _ h
        omega
      · intro s hs
        simp only [Finset.mem_Icc] at hs
        refine ⟨s - j, ?_, by omega⟩
        simp only [Finset.mem_range]
        omega
      · intro t _
        rfl
    rw [hbij, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htn : j + t ≤ n := by
      simp only [Finset.mem_range] at ht
      omega
    have hchoose : n.choose (j + t) * (j + t).choose j = n.choose j * (n - j).choose t := by
      have hc := Nat.choose_mul (n := n) (k := j + t) (s := j) (by omega)
      simpa [Nat.add_sub_cancel_left] using hc
    have hchooseq : (n.choose (j + t) : ℚ) * ((j + t).choose j : ℚ) =
        (n.choose j : ℚ) * ((n - j).choose t : ℚ) := by
      exact_mod_cast hchoose
    have hexp : j + t + m - 1 = (j + m - 1) + t := by omega
    have hpow : ((j : ℚ) / n) ^ (j + t + m - 1) =
        ((j : ℚ) / n) ^ (j + m - 1) * ((j : ℚ) / n) ^ t := by
      rw [hexp, pow_add]
    have hneg : (-1 : ℚ) ^ t * ((j : ℚ) / n) ^ t = (-(j : ℚ) / n) ^ t := by
      rw [← mul_pow]
      congr 1
      ring
    dsimp only [F]
    rw [show j + t - j = t by omega, hpow]
    calc
      (((j + t : ℕ) : ℚ) + m) * (n.choose (j + t) : ℚ) *
          ((-1 : ℚ) ^ t * ((j + t).choose j : ℚ) *
            (((j : ℚ) / n) ^ (j + m - 1) * ((j : ℚ) / n) ^ t)) * ((j + t : ℕ) : ℚ) / n
          = (((j : ℚ) + t + m) * ((j : ℚ) + t) *
              ((n.choose (j + t) : ℚ) * ((j + t).choose j : ℚ)) *
              (((j : ℚ) / n) ^ (j + m - 1) * ((-1 : ℚ) ^ t * ((j : ℚ) / n) ^ t))) / n := by
            push_cast; ring
      _ = (((j : ℚ) + t + m) * ((j : ℚ) + t) *
              ((n.choose j : ℚ) * ((n - j).choose t : ℚ)) *
              (((j : ℚ) / n) ^ (j + m - 1) * (-(j : ℚ) / n) ^ t)) / n := by
            rw [hchooseq, hneg]
      _ = (n.choose j : ℚ) * ((j : ℚ) / n) ^ (j + m - 1) / n *
            (((j : ℚ) + t + m) * ((j : ℚ) + t) * ((n - j).choose t : ℚ) * (-(j : ℚ) / n) ^ t) := by
            ring
  -- Step 4: split j = n and j ∈ Ico 1 n
  have hIcc_split : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hlhs1, hlhs2, Finset.sum_congr rfl hlhs3]
  nth_rw 1 [hIcc_split]
  rw [Finset.sum_insert (by simp)]
  have hjn_term :
      (n.choose n : ℚ) * ((n : ℚ) / n) ^ (n + m - 1) / n *
        ∑ t ∈ Finset.range (n - n + 1),
          ((n : ℚ) + t + m) * ((n : ℚ) + t) * ((n - n).choose t : ℚ) * (-(n : ℚ) / n) ^ t =
      (n : ℚ) + m := by
    simp only [Nat.sub_self, zero_add, Finset.sum_range_one, Nat.cast_zero, add_zero,
      Nat.cast_one, pow_zero, mul_one, Nat.choose_self]
    rw [div_self hn0, one_pow, mul_one]
    field_simp
  rw [hjn_term]
  have hico_eval : ∀ j ∈ Finset.Ico 1 n,
      (n.choose j : ℚ) * ((j : ℚ) / n) ^ (j + m - 1) / n *
        ∑ t ∈ Finset.range (n - j + 1),
          ((j : ℚ) + t + m) * ((j : ℚ) + t) * ((n - j).choose t : ℚ) * (-(j : ℚ) / n) ^ t =
      -(((n - j : ℕ) : ℚ) ^ (n - j - 1) * (n.choose (n - j) : ℚ) *
        (j : ℚ) ^ (j + m) / (n : ℚ) ^ (n + m - 1)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjn : j < n := (Finset.mem_Ico.mp hj).2
    rw [OMA.mo_128291_proof.quad_choose_sum n j m (n - j) hn0 (by omega) (by omega)]
    rw [← Nat.choose_symm (by omega : j ≤ n)]
    have hj_pow : (j : ℚ) ^ (j + m) = (j : ℚ) ^ (j + m - 1) * (j : ℚ) := by
      nth_rw 1 [show j + m = (j + m - 1) + 1 by omega]
      rw [pow_succ]
    have hn_pow : (n : ℚ) ^ (n + m - 1) =
        (n : ℚ) ^ (j + m - 1) * (n : ℚ) * (n : ℚ) ^ (n - j - 1) := by
      rw [← pow_succ, ← pow_add, show (j + m - 1) + 1 + (n - j - 1) = n + m - 1 by omega]
    rw [div_pow, div_pow, hj_pow, hn_pow]
    field_simp
  rw [Finset.sum_congr rfl hico_eval, Finset.sum_neg_distrib]
  -- Step 5: reindex k = n - j and add k = n term (which is 0)
  have hreidx_k :
      (∑ j ∈ Finset.Ico 1 n,
        ((n - j : ℕ) : ℚ) ^ (n - j - 1) * (n.choose (n - j) : ℚ) *
          (j : ℚ) ^ (j + m) / (n : ℚ) ^ (n + m - 1)) =
      ∑ k ∈ Finset.Ico 1 n,
        (k : ℚ) ^ (k - 1) * (n.choose k : ℚ) *
          ((n - k : ℕ) : ℚ) ^ (n + m - k) / (n : ℚ) ^ (n + m - 1) := by
    refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ico] at hj ⊢
      omega
    · intro j1 hj1 j2 hj2 h
      simp only [Finset.mem_Ico] at hj1 hj2
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      refine ⟨n - k, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hjn : j < n := (Finset.mem_Ico.mp hj).2
      have h1 : n - (n - j) = j := by omega
      have h2 : n + m - (n - j) = j + m := by omega
      rw [h1, h2]
  have hrhs_split :
      (∑ k ∈ Finset.Icc 1 n,
        (k : ℚ) ^ (k - 1) * (n.choose k : ℚ) *
          ((n - k : ℕ) : ℚ) ^ (n + m - k) / (n : ℚ) ^ (n + m - 1)) =
      ∑ k ∈ Finset.Ico 1 n,
        (k : ℚ) ^ (k - 1) * (n.choose k : ℚ) *
          ((n - k : ℕ) : ℚ) ^ (n + m - k) / (n : ℚ) ^ (n + m - 1) := by
    rw [hIcc_split, Finset.sum_insert (by simp)]
    rw [Nat.sub_self, Nat.add_sub_cancel_left]
    simp [zero_pow hm0]
  rw [hreidx_k, ← hrhs_split, ← sub_eq_add_neg]
