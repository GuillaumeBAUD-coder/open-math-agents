import OMAStatements.S_oeis_a273019

namespace OMA.P273019

open OMA.S_oeis_a273019

/-- `(n+1) * C(n,k) = (n+1-k) * C(n+1,k)` over the rationals. -/
lemma chA (n k : ℕ) :
    ((n : ℚ) + 1) * (n.choose k : ℚ) = ((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ) := by
  by_cases h : k ≤ n + 1
  · have e := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq n k)
    push_cast [Nat.cast_sub h] at e
    linear_combination e
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (n + 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    simp

/-- `(k+1) * C(n,k+1) = (n-k) * C(n,k)` over the rationals. -/
lemma chB (n k : ℕ) :
    ((k : ℚ) + 1) * (n.choose (k + 1) : ℚ) = ((n : ℚ) - k) * (n.choose k : ℚ) := by
  by_cases h : k ≤ n
  · have e := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub h] at e
    linear_combination e
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    simp

/-- `(k+2) * Cat(k+1) = 2*(2k+1) * Cat(k)`. -/
lemma catS (k : ℕ) :
    ((k : ℚ) + 2) * (catalan (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ) := by
  have e1 := congrArg (Nat.cast : ℕ → ℚ) (succ_mul_catalan_eq_centralBinom k)
  have e2 := congrArg (Nat.cast : ℕ → ℚ) (succ_mul_catalan_eq_centralBinom (k + 1))
  have e3 := congrArg (Nat.cast : ℕ → ℚ) (Nat.succ_mul_centralBinom_succ k)
  push_cast at e1 e2 e3
  have h : ((k : ℚ) + 1)
      * (((k : ℚ) + 2) * (catalan (k + 1) : ℚ) - 2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ)) = 0 := by
    linear_combination ((k : ℚ) + 1) * e2 + e3 - 2 * (2 * (k : ℚ) + 1) * e1
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hk
  · linear_combination h'

/-- The summand of the first sum. -/
noncomputable def F (m k : ℕ) : ℚ := (-1) ^ k * (m.choose k : ℚ) * (catalan k : ℚ)

/-- The first sum. -/
noncomputable def r (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), F m k

/-- The summand of the second sum. -/
noncomputable def Fu (m k : ℕ) : ℚ := (m.choose (2 * k) : ℚ) * (catalan k : ℚ)

/-- The second sum. -/
noncomputable def u (m : ℕ) : ℚ := ∑ k ∈ Finset.range (m + 1), Fu m k

lemma sum_ext0 (f : ℕ → ℚ) (K L : ℕ) (hKL : K ≤ L) (h0 : ∀ k, K ≤ k → f k = 0) :
    ∑ k ∈ Finset.range L, f k = ∑ k ∈ Finset.range K, f k := by
  symm
  apply Finset.sum_subset (Finset.range_mono hKL)
  intro k _ hk
  exact h0 k (Nat.le_of_not_lt (fun h => hk (Finset.mem_range.mpr h)))

lemma F_zero (m k : ℕ) (h : m < k) : F m k = 0 := by
  unfold F
  rw [Nat.choose_eq_zero_of_lt h]
  simp

lemma Fu_zero (m k : ℕ) (h : m < 2 * k) : Fu m k = 0 := by
  unfold Fu
  rw [Nat.choose_eq_zero_of_lt h]
  simp

lemma r_eq (m L : ℕ) (h : m + 1 ≤ L) : ∑ k ∈ Finset.range L, F m k = r m :=
  sum_ext0 (F m) (m + 1) L h (fun k hk => F_zero m k (by omega))

lemma u_eq (m L : ℕ) (h : m + 1 ≤ L) : ∑ k ∈ Finset.range L, Fu m k = u m :=
  sum_ext0 (Fu m) (m + 1) L h (fun k hk => Fu_zero m k (by omega))

lemma u_small (n : ℕ) : ∑ k ∈ Finset.range (n + 1), Fu (2 * n) k = u (2 * n) :=
  (sum_ext0 (Fu (2 * n)) (n + 1) (2 * n + 1) (by omega)
    (fun k hk => Fu_zero (2 * n) k (by omega))).symm

/-- The telescoping certificate for the first sum. -/
noncomputable def gr (m k : ℕ) : ℚ :=
  -((-1) ^ k * (k : ℚ) * ((k : ℚ) + 1) * (catalan k : ℚ) * ((m + 2).choose k : ℚ))

/-- The telescoping certificate for the second sum. -/
noncomputable def gu (m k : ℕ) : ℚ :=
  -(4 * (k : ℚ) * ((k : ℚ) + 1) * (catalan k : ℚ) * ((m + 2).choose (2 * k) : ℚ))

lemma key_r (m k : ℕ) :
    ((m : ℚ) + 2) * (((m : ℚ) + 3) * F (m + 2) k + 2 * ((m : ℚ) + 1) * F (m + 1) k
      - 3 * ((m : ℚ) + 1) * F m k) = gr m (k + 1) - gr m k := by
  have h1 := catS k
  have h2 := chB (m + 2) k
  have h3 := chA (m + 1) k
  have h4 := chA m k
  rw [show m + 1 + 1 = m + 2 from rfl] at h3
  push_cast at h2 h3 h4
  unfold F gr
  rw [pow_succ]
  push_cast
  linear_combination ((-1 : ℚ) ^ k) * ((-(((k : ℚ) + 1) * ((m + 2).choose (k + 1) : ℚ))) * h1
    - (2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ)) * h2
    + (2 * ((m : ℚ) + 1) * (catalan k : ℚ) - 3 * ((m : ℚ) + 1 - k) * (catalan k : ℚ)) * h3
    - (3 * ((m : ℚ) + 2) * (catalan k : ℚ)) * h4)

lemma key_u (m k : ℕ) :
    ((m : ℚ) + 2) * (((m : ℚ) + 4) * Fu (m + 2) k - (2 * (m : ℚ) + 5) * Fu (m + 1) k
      - 3 * ((m : ℚ) + 1) * Fu m k) = gu m (k + 1) - gu m k := by
  have h1 := catS k
  have h5 := chB (m + 2) (2 * k + 1)
  have h6 := chB (m + 2) (2 * k)
  have h3 := chA (m + 1) (2 * k)
  have h4 := chA m (2 * k)
  rw [show m + 1 + 1 = m + 2 from rfl] at h3
  push_cast at h5 h6 h3 h4
  unfold Fu gu
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
  push_cast
  linear_combination (4 * ((k : ℚ) + 1) * ((m + 2).choose (2 * k + 1 + 1) : ℚ)) * h1
    + (4 * (2 * (k : ℚ) + 1) * (catalan k : ℚ)) * h5
    + (4 * (catalan k : ℚ) * ((m : ℚ) + 1 - 2 * k)) * h6
    - ((2 * (m : ℚ) + 5) * (catalan k : ℚ) + 3 * ((m : ℚ) + 1 - 2 * k) * (catalan k : ℚ)) * h3
    - (3 * ((m : ℚ) + 2) * (catalan k : ℚ)) * h4

lemma gr_zero (m : ℕ) : gr m 0 = 0 := by
  unfold gr
  simp

lemma gr_top (m : ℕ) : gr m (m + 3) = 0 := by
  unfold gr
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

lemma gu_zero (m : ℕ) : gu m 0 = 0 := by
  unfold gu
  simp

lemma gu_top (m : ℕ) : gu m (m + 3) = 0 := by
  unfold gu
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

lemma rel_r (m : ℕ) :
    ((m : ℚ) + 3) * r (m + 2) + 2 * ((m : ℚ) + 1) * r (m + 1) - 3 * ((m : ℚ) + 1) * r m = 0 := by
  have hs : ∑ k ∈ Finset.range (m + 3), ((m : ℚ) + 2) * (((m : ℚ) + 3) * F (m + 2) k
      + 2 * ((m : ℚ) + 1) * F (m + 1) k - 3 * ((m : ℚ) + 1) * F m k) = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => key_r m k), Finset.sum_range_sub, gr_zero, gr_top,
      sub_zero]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, r_eq m (m + 3) (by omega), r_eq (m + 1) (m + 3) (by omega),
    r_eq (m + 2) (m + 3) (by omega)] at hs
  have hm : ((m : ℚ) + 2) ≠ 0 := by positivity
  rcases mul_eq_zero.mp hs with h | h
  · exact absurd h hm
  · exact h

lemma rel_u (m : ℕ) :
    ((m : ℚ) + 4) * u (m + 2) - (2 * (m : ℚ) + 5) * u (m + 1) - 3 * ((m : ℚ) + 1) * u m = 0 := by
  have hs : ∑ k ∈ Finset.range (m + 3), ((m : ℚ) + 2) * (((m : ℚ) + 4) * Fu (m + 2) k
      - (2 * (m : ℚ) + 5) * Fu (m + 1) k - 3 * ((m : ℚ) + 1) * Fu m k) = 0 := by
    rw [Finset.sum_congr rfl (fun k _ => key_u m k), Finset.sum_range_sub, gu_zero, gu_top,
      sub_zero]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, u_eq m (m + 3) (by omega), u_eq (m + 1) (m + 3) (by omega),
    u_eq (m + 2) (m + 3) (by omega)] at hs
  have hm : ((m : ℚ) + 2) ≠ 0 := by positivity
  rcases mul_eq_zero.mp hs with h | h
  · exact absurd h hm
  · exact h

lemma r0 : r 0 = 1 := by
  norm_num [r, F, Finset.sum_range_succ]

lemma r1 : r 1 = 0 := by
  norm_num [r, F, Finset.sum_range_succ]

lemma r2 : r 2 = 1 := by
  norm_num [r, F, Finset.sum_range_succ, catalan_two]

lemma u0 : u 0 = 1 := by
  norm_num [u, Fu, Finset.sum_range_succ]

lemma u1 : u 1 = 1 := by
  have h : Nat.choose 1 2 = 0 := by decide
  have h' : Nat.choose 1 (2 * 1) = 0 := by decide
  norm_num [u, Fu, Finset.sum_range_succ, h, h']

lemma uv (m : ℕ) : u m = (-1) ^ m * (r m - r (m + 1))
    ∧ u (m + 1) = (-1) ^ (m + 1) * (r (m + 1) - r (m + 2)) := by
  induction m with
  | zero =>
    norm_num [u0, u1, r0, r1, r2]
  | succ m ih =>
    obtain ⟨hm0, hm1⟩ := ih
    rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl]
    refine ⟨hm1, ?_⟩
    have hu := rel_u m
    have hr0 := rel_r m
    have hr1 := rel_r (m + 1)
    rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at hr1
    push_cast at hr1
    rw [pow_succ] at hm1
    rw [pow_succ, pow_succ]
    have h : ((m : ℚ) + 4)
        * (u (m + 2) - (-1) ^ m * (-1) * (-1) * (r (m + 2) - r (m + 3))) = 0 := by
      linear_combination hu + (2 * (m : ℚ) + 5) * hm1 + 3 * ((m : ℚ) + 1) * hm0
        - (-1) ^ m * hr0 + (-1) ^ m * hr1
    have hm : ((m : ℚ) + 4) ≠ 0 := by positivity
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hm
    · linear_combination h'

lemma hterm_succ (a b c z : ℚ) (k : ℕ) (hc : (ascPochhammer ℚ k).eval c ≠ 0)
    (hck : c + k ≠ 0) :
    hterm a b c z (k + 1)
      = hterm a b c z k * ((a + k) * (b + k) * z / ((c + k) * ((k : ℚ) + 1))) := by
  unfold hterm
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ascPochhammer_succ_eval,
    Nat.factorial_succ, pow_succ]
  have hf : (k.factorial : ℚ) ≠ 0 := by positivity
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  try ring

lemma poch2 (k : ℕ) : (ascPochhammer ℚ k).eval 2 ≠ 0 :=
  ne_of_gt (ascPochhammer_pos k 2 (by norm_num))

lemma t1 (m k : ℕ) : hterm (-(m : ℚ)) (1 / 2) 2 4 k = F m k := by
  induction k with
  | zero => simp [hterm, F]
  | succ k ih =>
    rw [hterm_succ _ _ _ _ k (poch2 k) (by positivity), ih]
    have hC := catS k
    have hB := chB m k
    unfold F
    rw [pow_succ, mul_div_assoc', div_eq_iff (by positivity)]
    linear_combination ((-1 : ℚ) ^ k * ((k : ℚ) + 1) * (m.choose (k + 1) : ℚ)) * hC
      + ((-1 : ℚ) ^ k * 2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ)) * hB

lemma t2 (n k : ℕ) : hterm (-(n : ℚ) + 1 / 2) (-(n : ℚ)) 2 4 k = Fu (2 * n) k := by
  induction k with
  | zero => simp [hterm, Fu]
  | succ k ih =>
    rw [hterm_succ _ _ _ _ k (poch2 k) (by positivity), ih]
    have hC := catS k
    have hB2 := chB (2 * n) (2 * k + 1)
    have hB1 := chB (2 * n) (2 * k)
    push_cast at hB2 hB1
    unfold Fu
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring, mul_div_assoc', div_eq_iff (by positivity)]
    linear_combination (-(((k : ℚ) + 1) * ((2 * n).choose (2 * k + 1 + 1) : ℚ))) * hC
      - ((2 * (k : ℚ) + 1) * (catalan k : ℚ)) * hB2
      - ((2 * (n : ℚ) - 2 * k - 1) * (catalan k : ℚ)) * hB1

lemma a_eq (n : ℕ) :
    a n = (2 * (n : ℚ) + 1) * r (2 * n) - 2 * (n : ℚ) * r (2 * n + 1) := by
  unfold a
  have e : (-2 * (n : ℚ) - 1) = -((2 * n + 1 : ℕ) : ℚ) := by
    push_cast
    ring
  rw [e, Finset.sum_congr rfl (fun k _ => t1 (2 * n + 1) k),
    Finset.sum_congr rfl (fun k _ => t2 n k), r_eq (2 * n + 1) (2 * n + 2) (by omega), u_small n,
    (uv (2 * n)).1, Even.neg_one_pow (even_two_mul n)]
  ring

end OMA.P273019

open OMA.S_oeis_a273019 OMA.P273019 in
theorem OMA.solution : type_of% @OMA.S_oeis_a273019.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have e1 : j + 3 - 1 = j + 2 := by omega
  have e2 : j + 3 - 2 = j + 1 := by omega
  have e3 : j + 3 - 3 = j := by omega
  rw [e1, e2, e3, a_eq (j + 3), a_eq (j + 2), a_eq (j + 1), a_eq j]
  have h0 := rel_r (2 * j)
  have h1 := rel_r (2 * j + 1)
  have h2 := rel_r (2 * j + 2)
  have h3 := rel_r (2 * j + 3)
  have h4 := rel_r (2 * j + 4)
  have h5 := rel_r (2 * j + 5)
  simp only [Nat.mul_add, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 ⊢
  push_cast at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination (-3 * ((j : ℚ) + 1) * (2 * (j : ℚ) + 3) * (2651 * (j : ℚ) + 4770)) * h0
    + (((j : ℚ) - 1) * (2 * (j : ℚ) + 3) * (2651 * (j : ℚ) + 4770)) * h1
    + (2 * (7230 * (j : ℚ) ^ 3 + 27156 * (j : ℚ) ^ 2 + 25525 * (j : ℚ) - 931)) * h2
    + (-(2 * (j : ℚ) + 5) * (2410 * (j : ℚ) ^ 2 + 3509 * (j : ℚ) + 3021)) * h3
    + ((241 * (j : ℚ) + 779) * (6 * (j : ℚ) ^ 2 + 39 * (j : ℚ) + 64)) * h4
    + (-((j : ℚ) + 3) * (2 * (j : ℚ) + 7) * (241 * (j : ℚ) + 779)) * h5
