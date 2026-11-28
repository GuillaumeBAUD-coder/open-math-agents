import OMAStatements.S_oeis_a302187

namespace OMA.S_oeis_a302187




/-! ### Free walks and the reflection principle -/

/-- The ±1 sequences of length k with sum -u. -/
def bin1 : ℕ → ℤ → ℤ
  | 0, u => if u = 0 then 1 else 0
  | k + 1, u => bin1 k (u + 1) + bin1 k (u - 1)

lemma bin1_neg : ∀ (k : ℕ) (u : ℤ), bin1 k (-u) = bin1 k u
  | 0, u => by simp [bin1]
  | k + 1, u => by
    rw [bin1, bin1, show -u + 1 = -(u - 1) by ring, show -u - 1 = -(u + 1) by ring, bin1_neg k, bin1_neg k,
      add_comm]

lemma bin1_high : ∀ (k q : ℕ), bin1 k (k + 2 * q + 2) = 0
  | 0, q => by
    rw [bin1, if_neg (by omega)]
  | k + 1, q => by
    rw [bin1, show ((k + 1 : ℕ) : ℤ) + 2 * q + 2 + 1 = k + 2 * ((q + 1 : ℕ) : ℤ) + 2 by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) + 2 * q + 2 - 1 = k + 2 * (q : ℤ) + 2 by push_cast; ring, bin1_high k, bin1_high k,
      add_zero]

lemma bin1_choose : ∀ (k p : ℕ), bin1 k (k - 2 * p) = k.choose p
  | 0, p => by
    rcases p with _ | p
    · simp [bin1]
    · rw [bin1, if_neg (by omega), Nat.choose_zero_succ, Nat.cast_zero]
  | k + 1, p => by
    rw [bin1]
    rcases p with _ | p
    · rw [show ((k + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) + 1 = k + 2 * ((0 : ℕ) : ℤ) + 2 by push_cast; ring,
        show ((k + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) - 1 = k - 2 * ((0 : ℕ) : ℤ) by push_cast; ring,
        bin1_high k, bin1_choose k]
      simp
    · rw [show ((k + 1 : ℕ) : ℤ) - 2 * ((p + 1 : ℕ) : ℤ) + 1 = k - 2 * (p : ℤ) by push_cast; ring,
        show ((k + 1 : ℕ) : ℤ) - 2 * ((p + 1 : ℕ) : ℤ) - 1 = k - 2 * ((p + 1 : ℕ) : ℤ) by push_cast; ring,
        bin1_choose k, bin1_choose k, Nat.choose_succ_succ', Nat.cast_add]

lemma bin1_odd : ∀ (k : ℕ) (j : ℤ), bin1 k (k - 2 * j - 1) = 0
  | 0, j => by
    rw [bin1, if_neg (by omega)]
  | k + 1, j => by
    rw [bin1, show ((k + 1 : ℕ) : ℤ) - 2 * j - 1 + 1 = k - 2 * (j - 1) - 1 by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) - 2 * j - 1 - 1 = k - 2 * j - 1 by push_cast; ring, bin1_odd k, bin1_odd k,
      add_zero]

/-- Free walks with the four steps ±x, ±y from (h, y) to the origin in k steps: in the coordinates
x + y and x - y they are two independent ±1 walks. -/
def P (k : ℕ) (h y : ℤ) : ℤ := bin1 k (h + y) * bin1 k (h - y)

lemma P_succ (k : ℕ) (h y : ℤ) :
    P (k + 1) h y = P k (h + 1) y + P k (h - 1) y + P k h (y + 1) + P k h (y - 1) := by
  simp only [P, bin1]
  rw [show h + 1 + y = h + y + 1 by ring, show h + 1 - y = h - y + 1 by ring,
    show h - 1 + y = h + y - 1 by ring, show h - 1 - y = h - y - 1 by ring,
    show h + (y + 1) = h + y + 1 by ring, show h - (y + 1) = h - y - 1 by ring,
    show h + (y - 1) = h + y - 1 by ring, show h - (y - 1) = h - y + 1 by ring]
  ring

/-- The walks from (h, y) that keep x ≥ 0, by reflection in x = -1. -/
def AB (k : ℕ) (h y : ℤ) : ℤ := P k h y - P k (h + 2) y

lemma AB_succ (k : ℕ) (h y : ℤ) :
    AB (k + 1) h y = AB k (h + 1) y + AB k (h - 1) y + AB k h (y + 1) + AB k h (y - 1) := by
  simp only [AB, P_succ]
  rw [show h + 2 + 1 = h + 1 + 2 by ring, show h + 2 - 1 = h + 1 by ring, show h - 1 + 2 = h + 1 by ring]
  ring

lemma AB_neg_one (k : ℕ) (y : ℤ) : AB k (-1) y = 0 := by
  simp only [AB, P]
  rw [show (-1 : ℤ) + y = -(1 - y) by ring, show (-1 : ℤ) - y = -(1 + y) by ring, bin1_neg, bin1_neg,
    show (-1 : ℤ) + 2 = 1 by norm_num]
  ring

/-! ### Back to the origin: only even lengths of the x, y part -/

/-- The 2D walks of type ab of length 2i: C(2i, i)^2 - C(2i, i+1)^2 = Cat(i) C(2i+1, i). -/
def w (i : ℕ) : ℤ := ((2 * i).choose i : ℤ) ^ 2 - ((2 * i).choose (i + 1) : ℤ) ^ 2

lemma AB_even (i : ℕ) : AB (2 * i) 0 0 = w i := by
  have h0 : bin1 (2 * i) 0 = (2 * i).choose i := by
    have := bin1_choose (2 * i) i
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * (i : ℤ) = 0 by push_cast; ring] at this
  have h2 : bin1 (2 * i) 2 = (2 * i).choose (i + 1) := by
    have := bin1_choose (2 * i) (i + 1)
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * ((i + 1 : ℕ) : ℤ) = -2 by push_cast; ring, bin1_neg] at this
  simp only [AB, P, w, add_zero, sub_zero, zero_add, h0, h2]
  ring

lemma AB_odd (i : ℕ) : AB (2 * i + 1) 0 0 = 0 := by
  have h0 : bin1 (2 * i + 1) 0 = 0 := by
    have := bin1_odd (2 * i + 1) i
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * (i : ℤ) - 1 = 0 by push_cast; ring] at this
  have h2 : bin1 (2 * i + 1) 2 = 0 := by
    have := bin1_odd (2 * i + 1) (i - 1)
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * ((i : ℤ) - 1) - 1 = 2 by push_cast; ring] at this
  simp only [AB, P, add_zero, sub_zero, zero_add, h0, h2]
  ring

lemma sum_even (g : ℕ → ℤ) (hg : ∀ i, g (2 * i + 1) = 0) :
    ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N), g k = ∑ i ∈ Finset.range N, g (2 * i)
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, sum_even g hg N,
      hg, add_zero, Finset.sum_range_succ]

/-! ### Walks from any start: the first-step recursion -/

lemma pt_zero {n : ℕ} (w : Fin n → Fin 6) : pt w 0 = 0 := by
  simp [pt]

lemma pt_cons {n : ℕ} (c : Fin 6) (w : Fin n → Fin 6) (t : ℕ) :
    pt (Fin.cons c w : Fin (n + 1) → Fin 6) (t + 1) = step c + pt w t := by
  simp [pt, Fin.sum_univ_succ]

/-- The walks of N steps from the point (h, y, z) that keep y ≥ 0 and z ≥ 0 and end with x = 0. -/
def cnt (N : ℕ) (h y z : ℤ) : ℕ :=
  (Finset.univ.filter (fun w : Fin N → Fin 6 =>
    (∀ t ≤ N, 0 ≤ y + (pt w t).2.1 ∧ 0 ≤ z + (pt w t).2.2) ∧ h + (pt w N).1 = 0)).card

lemma a_eq_cnt (n : ℕ) : a n = cnt n 0 0 0 := by
  simp only [a, cnt, zero_add]

lemma cnt_neg (N : ℕ) (h : ℤ) {y z : ℤ} (hh : y < 0 ∨ z < 0) : cnt N h y z = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hw
  have h0 := hw.1 0 (Nat.zero_le _)
  rw [pt_zero] at h0
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero] at h0
  omega

lemma cond_cons {N : ℕ} (c : Fin 6) (w : Fin N → Fin 6) (h y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ((∀ t ≤ N + 1, 0 ≤ y + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).2.1 ∧
        0 ≤ z + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).2.2) ∧
      h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).1 = 0) ↔
    ((∀ t ≤ N, 0 ≤ (y + (step c).2.1) + (pt w t).2.1 ∧ 0 ≤ (z + (step c).2.2) + (pt w t).2.2) ∧
      (h + (step c).1) + (pt w N).1 = 0) := by
  rw [pt_cons]
  simp only [Prod.fst_add, ← add_assoc]
  refine and_congr ⟨fun H t ht => ?_, fun H t ht => ?_⟩ Iff.rfl
  · have := H (t + 1) (by omega)
    simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc] at this
    exact this
  · rcases t with _ | t
    · simp only [pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
      exact ⟨hy, hz⟩
    · simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc]
      exact H t (by omega)

lemma cnt_succ_sum (N : ℕ) (h y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    cnt (N + 1) h y z = ∑ c : Fin 6, cnt N (h + (step c).1) (y + (step c).2.1) (z + (step c).2.2) := by
  rw [cnt, Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin 6)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [cnt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact if_congr (cond_cons c w h y z hy hz) rfl rfl

lemma cnt_succ (N : ℕ) (h y z : ℤ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (cnt (N + 1) h y z : ℤ) = cnt N (h + 1) y z + cnt N (h - 1) y z + cnt N h (y + 1) z + cnt N h (y - 1) z +
      cnt N h y (z + 1) + cnt N h y (z - 1) := by
  rw [cnt_succ_sum N h y z hy hz, Fin.sum_univ_six]
  simp [step]
  ring_nf

/-! ### The y- and z-steps: a walk in the quadrant with a free end, by reflection and a cumulative count -/

/-- The walks of m steps among ±y, ±z whose two coordinates end at least -s and -t (by recursion on m). -/
def Cum2 : ℕ → ℤ → ℤ → ℤ
  | 0, s, t => if 0 ≤ s ∧ 0 ≤ t then 1 else 0
  | m + 1, s, t => Cum2 m (s + 1) t + Cum2 m (s - 1) t + Cum2 m s (t + 1) + Cum2 m s (t - 1)

/-- The walks of exactly one final displacement are the free walks counted by P. -/
lemma Cum2_diff : ∀ (m : ℕ) (s t : ℤ),
    Cum2 m s t - Cum2 m (s - 1) t - Cum2 m s (t - 1) + Cum2 m (s - 1) (t - 1) = P m s t
  | 0, s, t => by
    simp only [Cum2, P, bin1]
    split_ifs <;> omega
  | m + 1, s, t => by
    have h1 := Cum2_diff m (s + 1) t
    have h2 := Cum2_diff m (s - 1) t
    have h3 := Cum2_diff m s (t + 1)
    have h4 := Cum2_diff m s (t - 1)
    rw [P_succ]
    simp only [Cum2]
    rw [show s + 1 - 1 = s by ring] at h1
    rw [show t + 1 - 1 = t by ring] at h3
    rw [show s - 1 + 1 = s by ring, show t - 1 + 1 = t by ring]
    linear_combination h1 + h2 + h3 + h4

/-- The walks of m steps among ±y, ±z from (y, z) that keep y ≥ 0 and z ≥ 0, by reflection in y = -1 and z = -1. -/
def Qq (m : ℕ) (y z : ℤ) : ℤ := Cum2 m y z - Cum2 m (-2 - y) z - Cum2 m y (-2 - z) + Cum2 m (-2 - y) (-2 - z)

lemma Qq_succ (m : ℕ) (y z : ℤ) :
    Qq (m + 1) y z = Qq m (y + 1) z + Qq m (y - 1) z + Qq m y (z + 1) + Qq m y (z - 1) := by
  simp only [Qq, Cum2]
  rw [show -2 - y + 1 = -1 - y by ring, show -2 - y - 1 = -3 - y by ring, show -2 - (y + 1) = -3 - y by ring,
    show -2 - (y - 1) = -1 - y by ring, show -2 - z + 1 = -1 - z by ring, show -2 - z - 1 = -3 - z by ring,
    show -2 - (z + 1) = -3 - z by ring, show -2 - (z - 1) = -1 - z by ring]
  ring

lemma Qq_neg_one_y (m : ℕ) (z : ℤ) : Qq m (-1) z = 0 := by
  rw [Qq, show (-2 : ℤ) - -1 = -1 by norm_num]
  ring

lemma Qq_neg_one_z (m : ℕ) (y : ℤ) : Qq m y (-1) = 0 := by
  rw [Qq, show (-2 : ℤ) - -1 = -1 by norm_num]
  ring

lemma Qq_zero (m : ℕ) : Qq m 0 0 = P m 0 0 + P m (-1) 0 + P m 0 (-1) + P m (-1) (-1) := by
  have h00 := Cum2_diff m 0 0
  have h10 := Cum2_diff m (-1) 0
  have h01 := Cum2_diff m 0 (-1)
  have h11 := Cum2_diff m (-1) (-1)
  rw [show (0 : ℤ) - 1 = -1 by norm_num] at h00 h10 h01
  rw [show (-1 : ℤ) - 1 = -2 by norm_num] at h10 h01 h11
  rw [Qq, show (-2 : ℤ) - 0 = -2 by norm_num]
  linear_combination h00 + h10 + h01 + h11

/-! ### The x-steps and the (y, z)-steps interleaved -/

/-- Tq N f y z = Sum_k C(N, k) f(k) Qq(N - k, y, z). -/
def Tq (N : ℕ) (f : ℕ → ℤ) (y z : ℤ) : ℤ := ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * Qq (N - k) y z

lemma Tq_succ (N : ℕ) (f : ℕ → ℤ) (y z : ℤ) :
    Tq (N + 1) f y z = Tq N (fun k => f (k + 1)) y z + Tq N f (y + 1) z + Tq N f (y - 1) z + Tq N f y (z + 1) +
      Tq N f y (z - 1) := by
  have h1 : Tq (N + 1) f y z = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * Qq (N - k) y z +
      ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * Qq (N - k) y z + f 0 * Qq (N + 1) y z := by
    rw [Tq, Finset.sum_range_succ', ← Finset.sum_add_distrib]
    simp only [Nat.choose_succ_succ', Nat.add_sub_add_right, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_add,
      Nat.cast_one, one_mul, add_mul]
  have h2 : Tq N f (y + 1) z + Tq N f (y - 1) z + Tq N f y (z + 1) + Tq N f y (z - 1) =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * Qq (N - k) y z + f 0 * Qq (N + 1) y z := by
    simp only [Tq, ← Finset.sum_add_distrib]
    have e : ∀ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * Qq (N - k) (y + 1) z +
        (N.choose k : ℤ) * f k * Qq (N - k) (y - 1) z + (N.choose k : ℤ) * f k * Qq (N - k) y (z + 1) +
        (N.choose k : ℤ) * f k * Qq (N - k) y (z - 1) = (N.choose k : ℤ) * f k * Qq (N + 1 - k) y z := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show N + 1 - k = N - k + 1 by omega, Qq_succ]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [show N + 1 - (k + 1) = N - k by omega]
  have h3 : ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * Qq (N - k) y z =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * Qq (N - k) y z := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero]
  have h4 : Tq N (fun k => f (k + 1)) y z =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * Qq (N - k) y z := rfl
  rw [h1, h3]
  linarith [h2, h4]

lemma cnt_zero (h y z : ℤ) (hy : -1 ≤ y) (hz : -1 ≤ z) : (cnt 0 h y z : ℤ) = bin1 0 h * Qq 0 y z := by
  have hc : cnt 0 h y z = if h = 0 ∧ 0 ≤ y ∧ 0 ≤ z then 1 else 0 := by
    rw [cnt, Finset.card_filter, Fintype.sum_unique]
    simp only [nonpos_iff_eq_zero, forall_eq, pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
    by_cases h0 : h = 0 <;> by_cases y0 : 0 ≤ y <;> by_cases z0 : 0 ≤ z <;> simp [h0, y0, z0]
  rw [hc]
  simp only [bin1, Qq, Cum2]
  split_ifs <;> omega

/-- The count from any start with y, z ≥ -1. -/
theorem cnt_eq (N : ℕ) : ∀ h y z : ℤ, -1 ≤ y → -1 ≤ z → (cnt N h y z : ℤ) = Tq N (fun k => bin1 k h) y z := by
  induction N with
  | zero =>
    intro h y z hy hz
    rw [cnt_zero h y z hy hz]
    simp [Tq]
  | succ N ih =>
    intro h y z hy hz
    rcases eq_or_lt_of_le hy with e | hy'
    · rw [← e, cnt_neg _ _ (Or.inl (by norm_num)), Nat.cast_zero]
      simp [Tq, Qq_neg_one_y]
    rcases eq_or_lt_of_le hz with e | hz'
    · rw [← e, cnt_neg _ _ (Or.inr (by norm_num)), Nat.cast_zero]
      simp [Tq, Qq_neg_one_z]
    have y0 : 0 ≤ y := by omega
    have z0 : 0 ≤ z := by omega
    have hs : Tq N (fun k => bin1 (k + 1) h) y z = Tq N (fun k => bin1 k (h + 1)) y z +
        Tq N (fun k => bin1 k (h - 1)) y z := by
      simp only [Tq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [bin1]; ring)
    rw [cnt_succ N h y z y0 z0, ih (h + 1) y z hy hz, ih (h - 1) y z hy hz, ih h (y + 1) z (by omega) hz,
      ih h (y - 1) z (by omega) hz, ih h y (z + 1) hy (by omega), ih h y (z - 1) hy (by omega), Tq_succ, hs]

/-! ### The even and the odd terms -/

lemma cb_succ (m : ℕ) : ((2 * (m + 1)).choose (m + 1) : ℤ) * ((m : ℤ) + 1) = 2 * (2 * m + 1) * ((2 * m).choose m : ℤ) := by
  have hb := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hb
  have e : ((m : ℤ) + 1) * ((2 * (m + 1)).choose (m + 1) : ℤ) = 2 * (2 * m + 1) * ((2 * m).choose m : ℤ) := by
    exact_mod_cast hb
  linear_combination e

lemma gq_succ (M : ℕ) : ((2 * (M + 1) + 1).choose (M + 1 + 1) : ℤ) * ((M : ℤ) + 2) =
    2 * (2 * M + 3) * ((2 * M + 1).choose (M + 1) : ℤ) := by
  have h1 := Nat.add_one_mul_choose_eq (2 * M + 2) (M + 1)
  rw [show 2 * M + 2 + 1 = 2 * (M + 1) + 1 by ring] at h1
  have h2 : (2 * M + 2).choose (M + 1) = 2 * (2 * M + 1).choose (M + 1) := by
    rw [show 2 * M + 2 = (2 * M + 1) + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
    ring
  rw [h2] at h1
  have e := congrArg (Nat.cast : ℕ → ℤ) h1
  push_cast at e ⊢
  linear_combination -e

lemma cb_half (M : ℕ) : ((2 * (M + 1)).choose (M + 1) : ℤ) = 2 * ((2 * M + 1).choose (M + 1) : ℤ) := by
  have h : (2 * (M + 1)).choose (M + 1) = 2 * (2 * M + 1).choose (M + 1) := by
    rw [show 2 * (M + 1) = (2 * M + 1) + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
    ring
  exact_mod_cast h

/-- The even terms: 2t x-steps (a ±1 walk back to 0, C(2t, t) of them) and 2M steps among ±y, ±z in the quadrant
(C(2M, M) C(2M+1, M+1) of them, M = N - t), interleaved. -/
def FE (N t : ℕ) : ℤ :=
  ((2 * N).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) * ((2 * (N - t)).choose (N - t) : ℤ) *
    ((2 * (N - t) + 1).choose (N - t + 1) : ℤ)

def SE (N : ℕ) : ℤ := ∑ t ∈ Finset.range (N + 1), FE N t

/-- The odd terms: 2t x-steps and 2M + 1 steps among ±y, ±z in the quadrant (2 C(2M+1, M+1)^2 of them). -/
def FO (N t : ℕ) : ℤ :=
  ((2 * N + 1).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) * (2 * ((2 * (N - t) + 1).choose (N - t + 1) : ℤ) ^ 2)

def SO (N : ℕ) : ℤ := ∑ t ∈ Finset.range (N + 1), FO N t

lemma bin1_even_zero (M : ℕ) : bin1 (2 * M) 0 = ((2 * M).choose M : ℤ) := by
  have := bin1_choose (2 * M) M
  rwa [show ((2 * M : ℕ) : ℤ) - 2 * (M : ℤ) = 0 by push_cast; ring] at this

lemma bin1_even_neg_two (M : ℕ) : bin1 (2 * M) (-2) = ((2 * M).choose (M + 1) : ℤ) := by
  have := bin1_choose (2 * M) (M + 1)
  rwa [show ((2 * M : ℕ) : ℤ) - 2 * ((M + 1 : ℕ) : ℤ) = -2 by push_cast; ring] at this

lemma bin1_even_neg_one (M : ℕ) : bin1 (2 * M) (-1) = 0 := by
  have := bin1_odd (2 * M) M
  rwa [show ((2 * M : ℕ) : ℤ) - 2 * (M : ℤ) - 1 = -1 by push_cast; ring] at this

lemma bin1_even_one (M : ℕ) : bin1 (2 * M) 1 = 0 := by
  rw [← bin1_neg, bin1_even_neg_one]

lemma bin1_odd_zero (M : ℕ) : bin1 (2 * M + 1) 0 = 0 := by
  have := bin1_odd (2 * M + 1) M
  rwa [show ((2 * M + 1 : ℕ) : ℤ) - 2 * (M : ℤ) - 1 = 0 by push_cast; ring] at this

lemma bin1_odd_neg_two (M : ℕ) : bin1 (2 * M + 1) (-2) = 0 := by
  have := bin1_odd (2 * M + 1) ((M : ℤ) + 1)
  rwa [show ((2 * M + 1 : ℕ) : ℤ) - 2 * ((M : ℤ) + 1) - 1 = -2 by push_cast; ring] at this

lemma bin1_odd_neg_one (M : ℕ) : bin1 (2 * M + 1) (-1) = ((2 * M + 1).choose (M + 1) : ℤ) := by
  have := bin1_choose (2 * M + 1) (M + 1)
  rwa [show ((2 * M + 1 : ℕ) : ℤ) - 2 * ((M + 1 : ℕ) : ℤ) = -1 by push_cast; ring] at this

lemma bin1_odd_one (M : ℕ) : bin1 (2 * M + 1) 1 = ((2 * M + 1).choose (M + 1) : ℤ) := by
  rw [← bin1_neg, bin1_odd_neg_one]

/-- The (y, z)-walks of even length that stay in the quadrant: C(2M, M) C(2M+1, M+1). -/
lemma Qq_even (M : ℕ) : Qq (2 * M) 0 0 = ((2 * M).choose M : ℤ) * ((2 * M + 1).choose (M + 1) : ℤ) := by
  rw [Qq_zero]
  simp only [P]
  rw [show (0 : ℤ) + 0 = 0 by norm_num, show (0 : ℤ) - 0 = 0 by norm_num, show (-1 : ℤ) + 0 = -1 by norm_num,
    show (-1 : ℤ) - 0 = -1 by norm_num, show (0 : ℤ) + -1 = -1 by norm_num, show (0 : ℤ) - -1 = 1 by norm_num,
    show (-1 : ℤ) + -1 = -2 by norm_num, show (-1 : ℤ) - -1 = 0 by norm_num, bin1_even_zero, bin1_even_neg_one,
    bin1_even_one, bin1_even_neg_two, Nat.choose_succ_succ', Nat.cast_add]
  ring

/-- The (y, z)-walks of odd length that stay in the quadrant: 2 C(2M+1, M+1)^2. -/
lemma Qq_odd (M : ℕ) : Qq (2 * M + 1) 0 0 = 2 * ((2 * M + 1).choose (M + 1) : ℤ) ^ 2 := by
  rw [Qq_zero]
  simp only [P]
  rw [show (0 : ℤ) + 0 = 0 by norm_num, show (0 : ℤ) - 0 = 0 by norm_num, show (-1 : ℤ) + 0 = -1 by norm_num,
    show (-1 : ℤ) - 0 = -1 by norm_num, show (0 : ℤ) + -1 = -1 by norm_num, show (0 : ℤ) - -1 = 1 by norm_num,
    show (-1 : ℤ) + -1 = -2 by norm_num, show (-1 : ℤ) - -1 = 0 by norm_num, bin1_odd_zero, bin1_odd_neg_one,
    bin1_odd_one, bin1_odd_neg_two]
  ring

/-- The even terms of the entry. -/
theorem a_even (N : ℕ) : (a (2 * N) : ℤ) = SE N := by
  rw [a_eq_cnt, cnt_eq (2 * N) 0 0 0 (by norm_num) (by norm_num), Tq]
  have hz : ∀ k ∈ Finset.range (2 * (N + 1)), k ∉ Finset.range (2 * N + 1) →
      ((2 * N).choose k : ℤ) * bin1 k 0 * Qq (2 * N - k) 0 0 = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega)) hz,
    sum_even (fun k => ((2 * N).choose k : ℤ) * bin1 k 0 * Qq (2 * N - k) 0 0)
      (fun i => by simp [bin1_odd_zero]) (N + 1)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [bin1_even_zero, FE, show 2 * N - 2 * t = 2 * (N - t) by omega, Qq_even]
  ring

/-- The odd terms of the entry. -/
theorem a_odd (N : ℕ) : (a (2 * N + 1) : ℤ) = SO N := by
  rw [a_eq_cnt, cnt_eq (2 * N + 1) 0 0 0 (by norm_num) (by norm_num), Tq, show 2 * N + 1 + 1 = 2 * (N + 1) by ring,
    sum_even (fun k => ((2 * N + 1).choose k : ℤ) * bin1 k 0 * Qq (2 * N + 1 - k) 0 0)
      (fun i => by simp [bin1_odd_zero]) (N + 1)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [bin1_even_zero, FO, show 2 * N + 1 - 2 * t = 2 * (N - t) + 1 by omega, Qq_odd]

/-! ### Shift relations -/

/-- One more step in n for the even summand. -/
lemma FEn (n t : ℕ) : FE (n + 1) t * (((n : ℤ) - t + 1) ^ 2 * ((n : ℤ) - t + 2)) =
    4 * ((n : ℤ) + 1) * (2 * n + 1) * (2 * ((n : ℤ) - t) + 3) * FE n t := by
  rcases Nat.lt_or_ge n t with h | h
  · have h0 : FE n t = 0 := by
      rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [h0, mul_zero]
    rcases Nat.eq_or_lt_of_le h with e | e
    · subst e
      push_cast
      ring
    · rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · obtain ⟨M, rfl⟩ : ∃ M, n = t + M := ⟨n - t, by omega⟩
    simp only [FE]
    rw [show t + M + 1 - t = M + 1 by omega, show t + M - t = M by omega]
    have hA1 := Nat.choose_mul_succ_eq (2 * (t + M)) (2 * t)
    have hA2 := Nat.choose_mul_succ_eq (2 * (t + M) + 1) (2 * t)
    rw [show 2 * (t + M) + 1 - 2 * t = 2 * M + 1 by omega] at hA1
    rw [show 2 * (t + M) + 1 + 1 - 2 * t = 2 * M + 2 by omega,
      show 2 * (t + M) + 1 + 1 = 2 * (t + M + 1) by ring] at hA2
    have eA1 : ((2 * (t + M)).choose (2 * t) : ℤ) * (2 * ((t : ℤ) + M) + 1) =
        ((2 * (t + M) + 1).choose (2 * t) : ℤ) * (2 * M + 1) := by
      exact_mod_cast hA1
    have eA2 : ((2 * (t + M) + 1).choose (2 * t) : ℤ) * (2 * ((t : ℤ) + M) + 2) =
        ((2 * (t + M + 1)).choose (2 * t) : ℤ) * (2 * M + 2) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) hA2
      push_cast at e ⊢
      linear_combination e
    have eB := cb_succ M
    have eG := gq_succ M
    push_cast
    linear_combination (((M : ℤ) + 1) * ((2 * (t + M + 1)).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) *
        ((2 * (M + 1) + 1).choose (M + 1 + 1) : ℤ) * ((M : ℤ) + 2)) * eB +
      (2 * (2 * (M : ℤ) + 1) * ((M : ℤ) + 1) * ((2 * (t + M + 1)).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) *
        ((2 * M).choose M : ℤ)) * eG -
      (2 * (2 * (M : ℤ) + 1) * (2 * M + 3) * ((2 * t).choose t : ℤ) * ((2 * M).choose M : ℤ) *
        ((2 * M + 1).choose (M + 1) : ℤ)) * eA2 -
      (2 * (2 * (M : ℤ) + 3) * (2 * ((t : ℤ) + M) + 2) * ((2 * t).choose t : ℤ) * ((2 * M).choose M : ℤ) *
        ((2 * M + 1).choose (M + 1) : ℤ)) * eA1

/-- One more step in t for the even summand. -/
lemma FEk (n t : ℕ) : FE n (t + 1) * (2 * ((t : ℤ) + 1) ^ 2 * (2 * ((n : ℤ) - t) + 1)) =
    ((n : ℤ) - t) ^ 2 * ((n : ℤ) - t + 1) * FE n t := by
  rcases Nat.lt_or_ge t n with h | h
  · obtain ⟨M, rfl⟩ : ∃ M, n = t + 1 + M := ⟨n - t - 1, by omega⟩
    simp only [FE]
    rw [show t + 1 + M - (t + 1) = M by omega, show t + 1 + M - t = M + 1 by omega]
    have e1 := Nat.choose_succ_right_eq (2 * (t + 1 + M)) (2 * t)
    have e2 := Nat.choose_succ_right_eq (2 * (t + 1 + M)) (2 * t + 1)
    rw [show 2 * (t + 1 + M) - 2 * t = 2 * M + 2 by omega] at e1
    rw [show 2 * (t + 1 + M) - (2 * t + 1) = 2 * M + 1 by omega, show 2 * t + 1 + 1 = 2 * (t + 1) by ring] at e2
    have e1' : ((2 * (t + 1 + M)).choose (2 * t + 1) : ℤ) * (2 * t + 1) =
        ((2 * (t + 1 + M)).choose (2 * t) : ℤ) * (2 * M + 2) := by
      exact_mod_cast e1
    have e2' : ((2 * (t + 1 + M)).choose (2 * (t + 1)) : ℤ) * (2 * t + 2) =
        ((2 * (t + 1 + M)).choose (2 * t + 1) : ℤ) * (2 * M + 1) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) e2
      push_cast at e ⊢
      linear_combination e
    have eb := cb_succ t
    have eB := cb_succ M
    have eG := gq_succ M
    push_cast
    linear_combination (((2 * (t + 1)).choose (t + 1) : ℤ) * ((t : ℤ) + 1) * ((2 * M).choose M : ℤ) *
        ((2 * M + 1).choose (M + 1) : ℤ) * (2 * (M : ℤ) + 3)) * e2' +
      (((2 * (t + 1 + M)).choose (2 * t + 1) : ℤ) * (2 * (M : ℤ) + 1) * ((2 * M).choose M : ℤ) *
        ((2 * M + 1).choose (M + 1) : ℤ) * (2 * (M : ℤ) + 3)) * eb +
      (2 * (2 * (M : ℤ) + 1) * ((2 * t).choose t : ℤ) * ((2 * M).choose M : ℤ) * ((2 * M + 1).choose (M + 1) : ℤ) *
        (2 * (M : ℤ) + 3)) * e1' -
      (((M : ℤ) + 1) * ((2 * (t + 1 + M)).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) *
        ((2 * (M + 1) + 1).choose (M + 1 + 1) : ℤ) * ((M : ℤ) + 2)) * eB -
      (((M : ℤ) + 1) * ((2 * (t + 1 + M)).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) * 2 * (2 * (M : ℤ) + 1) *
        ((2 * M).choose M : ℤ)) * eG
  · rcases Nat.eq_or_lt_of_le h with e | e
    · subst e
      have h1 : FE n (n + 1) = 0 := by
        rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [h1]
      ring
    · have h0 : FE n t = 0 := by
        rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have h1 : FE n (t + 1) = 0 := by
        rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [h0, h1]
      ring

/-- The odd summand against the even one. -/
lemma R1 (n t : ℕ) : FO n t * (2 * ((n : ℤ) + 1) * (2 * ((n : ℤ) - t) + 3)) =
    FE (n + 1) t * (((n : ℤ) - t + 1) * ((n : ℤ) - t + 2)) := by
  rcases Nat.lt_or_ge n t with h | h
  · have h0 : FO n t = 0 := by
      rw [FO, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [h0, zero_mul]
    rcases Nat.eq_or_lt_of_le h with e | e
    · subst e
      push_cast
      ring
    · rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · obtain ⟨M, rfl⟩ : ∃ M, n = t + M := ⟨n - t, by omega⟩
    simp only [FO, FE]
    rw [show t + M - t = M by omega, show t + M + 1 - t = M + 1 by omega]
    have hA2 := Nat.choose_mul_succ_eq (2 * (t + M) + 1) (2 * t)
    rw [show 2 * (t + M) + 1 + 1 - 2 * t = 2 * M + 2 by omega,
      show 2 * (t + M) + 1 + 1 = 2 * (t + M + 1) by ring] at hA2
    have eA2 : ((2 * (t + M) + 1).choose (2 * t) : ℤ) * (2 * ((t : ℤ) + M) + 2) =
        ((2 * (t + M + 1)).choose (2 * t) : ℤ) * (2 * M + 2) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) hA2
      push_cast at e ⊢
      linear_combination e
    have eH := cb_half M
    have eG := gq_succ M
    push_cast
    linear_combination (2 * (2 * (M : ℤ) + 3) * ((2 * t).choose t : ℤ) * ((2 * M + 1).choose (M + 1) : ℤ) ^ 2) * eA2 -
      (((2 * (t + M + 1)).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) * ((M : ℤ) + 1) * ((M : ℤ) + 2) *
        ((2 * (M + 1) + 1).choose (M + 1 + 1) : ℤ)) * eH -
      (2 * ((2 * (t + M + 1)).choose (2 * t) : ℤ) * ((2 * t).choose t : ℤ) * ((M : ℤ) + 1) *
        ((2 * M + 1).choose (M + 1) : ℤ)) * eG

/-! ### The order-2 operator M of the even terms, an order-3 telescoper, and its certificate -/

/-- M at m: M(m) = p0 SE(m) + p1 SE(m+1) + p2 SE(m+2). -/
def p0 (m : ℕ) : ℤ :=
  5508 + 24516 * (m : ℤ) + 38736 * (m : ℤ) ^ 2 + 27792 * (m : ℤ) ^ 3 + 9216 * (m : ℤ) ^ 4 + 1152 * (m : ℤ) ^ 5
def p1 (m : ℕ) : ℤ :=
  -6588 - 18552 * (m : ℤ) - 20660 * (m : ℤ) ^ 2 - 11320 * (m : ℤ) ^ 3 - 3040 * (m : ℤ) ^ 4 - 320 * (m : ℤ) ^ 5
def p2 (m : ℕ) : ℤ :=
  342 + 831 * (m : ℤ) + 800 * (m : ℤ) ^ 2 + 379 * (m : ℤ) ^ 3 + 88 * (m : ℤ) ^ 4 + 8 * (m : ℤ) ^ 5

/-- The certificate: G(m, k) = cp(m, k) / ((2m - 2k + 5)(2m - 2k + 7)) FE(m + 3, k), cp a polynomial in k. -/
def cp (m k : ℕ) : ℚ :=
  ((-24235200 - 75216834 * (m : ℚ) - 103318146 * (m : ℚ) ^ 2 - 82435807 * (m : ℚ) ^ 3 - 42104357 * (m : ℚ) ^ 4
      - 14276375 * (m : ℚ) ^ 5 - 3213853 * (m : ℚ) ^ 6 - 463260 * (m : ℚ) ^ 7 - 38808 * (m : ℚ) ^ 8
      - 1440 * (m : ℚ) ^ 9) * (k : ℚ) ^ 2 + (21589422 + 58602226 * (m : ℚ) + 69226729 * (m : ℚ) ^ 2
      + 46478230 * (m : ℚ) ^ 3 + 19396463 * (m : ℚ) ^ 4 + 5152138 * (m : ℚ) ^ 5 + 850720 * (m : ℚ) ^ 6
      + 79856 * (m : ℚ) ^ 7 + 3264 * (m : ℚ) ^ 8) * (k : ℚ) ^ 3 + (-5317260 - 11889301 * (m : ℚ)
      - 11221080 * (m : ℚ) ^ 2 - 5777210 * (m : ℚ) ^ 3 - 1745343 * (m : ℚ) ^ 4 - 307676 * (m : ℚ) ^ 5
      - 29064 * (m : ℚ) ^ 6 - 1120 * (m : ℚ) ^ 7) * (k : ℚ) ^ 4 + (-309417 - 1014310 * (m : ℚ)
      - 1209126 * (m : ℚ) ^ 2 - 713924 * (m : ℚ) ^ 3 - 225984 * (m : ℚ) ^ 4 - 36832 * (m : ℚ) ^ 5
      - 2432 * (m : ℚ) ^ 6) * (k : ℚ) ^ 5 + (315537 + 610753 * (m : ℚ) + 467781 * (m : ℚ) ^ 2
      + 177292 * (m : ℚ) ^ 3 + 33240 * (m : ℚ) ^ 4 + 2464 * (m : ℚ) ^ 5) * (k : ℚ) ^ 6 + (-46665
      - 68934 * (m : ℚ) - 37984 * (m : ℚ) ^ 2 - 9232 * (m : ℚ) ^ 3 - 832 * (m : ℚ) ^ 4) * (k : ℚ) ^ 7 + (2295
      + 2412 * (m : ℚ) + 840 * (m : ℚ) ^ 2 + 96 * (m : ℚ) ^ 3) * (k : ℚ) ^ 8) /
    (4 * ((m : ℚ) + 2) * ((m : ℚ) + 3))

/-- The telescoper (4m+11)(m+3) M(m+1) - 2(2m+5)(4m+15) M(m). -/
def t0 (m : ℕ) : ℤ := -2 * (2 * (m : ℤ) + 5) * (4 * m + 15) * p0 m
def t1 (m : ℕ) : ℤ := -2 * (2 * (m : ℤ) + 5) * (4 * m + 15) * p1 m + (4 * (m : ℤ) + 11) * (m + 3) * p0 (m + 1)
def t2 (m : ℕ) : ℤ := -2 * (2 * (m : ℤ) + 5) * (4 * m + 15) * p2 m + (4 * (m : ℤ) + 11) * (m + 3) * p1 (m + 1)
def t3 (m : ℕ) : ℤ := (4 * (m : ℤ) + 11) * (m + 3) * p2 (m + 1)

def G (m k : ℕ) : ℚ := cp m k / ((2 * (m : ℚ) - 2 * k + 5) * (2 * (m : ℚ) - 2 * k + 7)) * FE (m + 3) k

/-- The certificate identity, term by term, for every k. -/
lemma cert (m k : ℕ) :
    (t0 m : ℚ) * FE m k + t1 m * FE (m + 1) k + t2 m * FE (m + 2) k + t3 m * FE (m + 3) k =
      G m (k + 1) - G m k := by
  have e2 := FEn (m + 2) k
  have e1 := FEn (m + 1) k
  have e0 := FEn m k
  have ey := FEk (m + 3) k
  rw [show m + 2 + 1 = m + 3 from rfl] at e2
  rw [show m + 1 + 1 = m + 2 from rfl] at e1
  push_cast at e2 e1 e0 ey
  have n7 : (2 * (m : ℚ) - 2 * k + 7) ≠ 0 := by
    have : (2 * (m : ℤ) - 2 * k + 7) ≠ 0 := by omega
    exact_mod_cast this
  have n5 : (2 * (m : ℚ) - 2 * k + 5) ≠ 0 := by
    have : (2 * (m : ℤ) - 2 * k + 5) ≠ 0 := by omega
    exact_mod_cast this
  have n3 : (2 * (m : ℚ) - 2 * k + 3) ≠ 0 := by
    have : (2 * (m : ℤ) - 2 * k + 3) ≠ 0 := by omega
    exact_mod_cast this
  have q2 : (FE (m + 2) k : ℚ) = FE (m + 3) k * (((m : ℚ) - k + 3) ^ 2 * ((m : ℚ) - k + 4)) /
      (4 * ((m : ℚ) + 3) * (2 * m + 5) * (2 * m - 2 * k + 7)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n7)]
    exact_mod_cast (by linear_combination -e2 :
      FE (m + 2) k * (4 * ((m : ℤ) + 3) * (2 * m + 5) * (2 * m - 2 * k + 7)) =
        FE (m + 3) k * (((m : ℤ) - k + 3) ^ 2 * ((m : ℤ) - k + 4)))
  have q1 : (FE (m + 1) k : ℚ) = FE (m + 2) k * (((m : ℚ) - k + 2) ^ 2 * ((m : ℚ) - k + 3)) /
      (4 * ((m : ℚ) + 2) * (2 * m + 3) * (2 * m - 2 * k + 5)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n5)]
    exact_mod_cast (by linear_combination -e1 :
      FE (m + 1) k * (4 * ((m : ℤ) + 2) * (2 * m + 3) * (2 * m - 2 * k + 5)) =
        FE (m + 2) k * (((m : ℤ) - k + 2) ^ 2 * ((m : ℤ) - k + 3)))
  have q0 : (FE m k : ℚ) = FE (m + 1) k * (((m : ℚ) - k + 1) ^ 2 * ((m : ℚ) - k + 2)) /
      (4 * ((m : ℚ) + 1) * (2 * m + 1) * (2 * m - 2 * k + 3)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n3)]
    exact_mod_cast (by linear_combination -e0 :
      FE m k * (4 * ((m : ℤ) + 1) * (2 * m + 1) * (2 * m - 2 * k + 3)) =
        FE (m + 1) k * (((m : ℤ) - k + 1) ^ 2 * ((m : ℤ) - k + 2)))
  have qy : (FE (m + 3) (k + 1) : ℚ) =
      ((m : ℚ) - k + 3) ^ 2 * ((m : ℚ) - k + 4) * FE (m + 3) k / (2 * ((k : ℚ) + 1) ^ 2 * (2 * m - 2 * k + 7)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n7)]
    exact_mod_cast (by linear_combination ey :
      FE (m + 3) (k + 1) * (2 * ((k : ℤ) + 1) ^ 2 * (2 * m - 2 * k + 7)) =
        ((m : ℤ) - k + 3) ^ 2 * ((m : ℤ) - k + 4) * FE (m + 3) k)
  have n5' : (2 * (m : ℚ) - 2 * ((k + 1 : ℕ) : ℚ) + 5) = 2 * m - 2 * k + 3 := by push_cast; ring
  have n7' : (2 * (m : ℚ) - 2 * ((k + 1 : ℕ) : ℚ) + 7) = 2 * m - 2 * k + 5 := by push_cast; ring
  -- field_simp writes 2m - 2k + c as 2(m - k) + c and needs that form to be nonzero
  have m7 : 2 * ((m : ℚ) - k) + 7 ≠ 0 := by rw [mul_sub]; exact n7
  have m5 : 2 * ((m : ℚ) - k) + 5 ≠ 0 := by rw [mul_sub]; exact n5
  have m3 : 2 * ((m : ℚ) - k) + 3 ≠ 0 := by rw [mul_sub]; exact n3
  simp only [G]
  rw [n5', n7', q0, q1, q2, qy]
  simp only [cp, t0, t1, t2, t3, p0, p1, p2]
  push_cast
  field_simp
  ring

/-- The telescoper annihilates the sum. -/
theorem rec_T (m : ℕ) : t0 m * SE m + t1 m * SE (m + 1) + t2 m * SE (m + 2) + t3 m * SE (m + 3) = 0 := by
  have ext : ∀ n, n ≤ m + 3 → (SE n : ℚ) = ∑ k ∈ Finset.range (m + 4), (FE n k : ℚ) := by
    intro n hn
    rw [SE, Int.cast_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun k _ hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have g0 : G m 0 = 0 := by simp [G, cp]
  have g1 : G m (m + 4) = 0 := by
    rw [G, FE, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hq : (t0 m : ℚ) * SE m + t1 m * SE (m + 1) + t2 m * SE (m + 2) + t3 m * SE (m + 3) = 0 := by
    rw [ext m (by omega), ext (m + 1) (by omega), ext (m + 2) (by omega), ext (m + 3) le_rfl,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => cert m k),
      Finset.sum_range_sub (G m), g0, g1, sub_zero]
  exact_mod_cast hq

/-! ### M annihilates the even terms -/

/-- M at m. -/
def e (m : ℕ) : ℤ := p0 m * SE m + p1 m * SE (m + 1) + p2 m * SE (m + 2)

lemma e_succ (m : ℕ) :
    (4 * (m : ℤ) + 11) * ((m : ℤ) + 3) * e (m + 1) = 2 * (2 * (m : ℤ) + 5) * (4 * m + 15) * e m := by
  have h := rec_T m
  simp only [e, t0, t1, t2, t3] at h ⊢
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl]
  linear_combination h

lemma e_zero : e 0 = 0 := by
  decide +kernel

lemma e_eq_zero : ∀ m, e m = 0
  | 0 => e_zero
  | m + 1 => by
    have h := e_succ m
    rw [e_eq_zero m, mul_zero] at h
    have hne : (4 * (m : ℤ) + 11) * ((m : ℤ) + 3) ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left hne

/-! ### The cross relation between the odd and the even terms -/

/-- The certificate of (N+2)^2 X(N+1) - 2(N+1)(2N+5) X(N): Gx(N, k) = cpx(N, k) / (2N - 2k + 5) FE(N + 2, k). -/
def cpx (N k : ℕ) : ℚ :=
  ((-900 - 1930 * (N : ℚ) - 1628 * (N : ℚ) ^ 2 - 680 * (N : ℚ) ^ 3 - 142 * (N : ℚ) ^ 4
      - 12 * (N : ℚ) ^ 5) * (k : ℚ) ^ 2 + (302 + 460 * (N : ℚ) + 246 * (N : ℚ) ^ 2 + 54 * (N : ℚ) ^ 3
      + 4 * (N : ℚ) ^ 4) * (k : ℚ) ^ 3 + (40 + 96 * (N : ℚ) + 62 * (N : ℚ) ^ 2
      + 12 * (N : ℚ) ^ 3) * (k : ℚ) ^ 4 + (-10 - 14 * (N : ℚ) - 4 * (N : ℚ) ^ 2) * (k : ℚ) ^ 5) /
    (4 * ((N : ℚ) + 2) * (2 * (N : ℚ) + 3))

/-- The cross relation, to be shown zero. -/
def X (N : ℕ) : ℤ :=
  ((N : ℤ) + 2) ^ 2 * SE (N + 1) + 6 * (2 * (N : ℤ) + 1) * ((N : ℤ) + 1) * SE N - (8 * (N : ℤ) ^ 2 + 24 * N + 19) * SO N

/-- Its summand. -/
def xk (N k : ℕ) : ℚ :=
  ((N : ℚ) + 2) ^ 2 * FE (N + 1) k + 6 * (2 * (N : ℚ) + 1) * ((N : ℚ) + 1) * FE N k -
    (8 * (N : ℚ) ^ 2 + 24 * N + 19) * FO N k

def Gx (N k : ℕ) : ℚ := cpx N k / (2 * (N : ℚ) - 2 * k + 5) * FE (N + 2) k

lemma certx (N k : ℕ) :
    ((N : ℚ) + 2) ^ 2 * xk (N + 1) k - 2 * ((N : ℚ) + 1) * (2 * (N : ℚ) + 5) * xk N k = Gx N (k + 1) - Gx N k := by
  simp only [xk]
  push_cast
  rw [show N + 1 + 1 = N + 2 from rfl]
  have r1 := R1 (N + 1) k
  have r0 := R1 N k
  have f1 := FEn (N + 1) k
  have f0 := FEn N k
  have fy := FEk (N + 2) k
  rw [show N + 1 + 1 = N + 2 from rfl] at r1 f1
  push_cast at r1 r0 f1 f0 fy
  have n5 : (2 * (N : ℚ) - 2 * k + 5) ≠ 0 := by
    have : (2 * (N : ℤ) - 2 * k + 5) ≠ 0 := by omega
    exact_mod_cast this
  have n3 : (2 * (N : ℚ) - 2 * k + 3) ≠ 0 := by
    have : (2 * (N : ℤ) - 2 * k + 3) ≠ 0 := by omega
    exact_mod_cast this
  have qO1 : (FO (N + 1) k : ℚ) = FE (N + 2) k * (((N : ℚ) - k + 2) * ((N : ℚ) - k + 3)) /
      (2 * ((N : ℚ) + 2) * (2 * N - 2 * k + 5)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n5)]
    exact_mod_cast (by linear_combination r1 :
      FO (N + 1) k * (2 * ((N : ℤ) + 2) * (2 * N - 2 * k + 5)) =
        FE (N + 2) k * (((N : ℤ) - k + 2) * ((N : ℤ) - k + 3)))
  have qF1 : (FE (N + 1) k : ℚ) = FE (N + 2) k * (((N : ℚ) - k + 2) ^ 2 * ((N : ℚ) - k + 3)) /
      (4 * ((N : ℚ) + 2) * (2 * N + 3) * (2 * N - 2 * k + 5)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n5)]
    exact_mod_cast (by linear_combination -f1 :
      FE (N + 1) k * (4 * ((N : ℤ) + 2) * (2 * N + 3) * (2 * N - 2 * k + 5)) =
        FE (N + 2) k * (((N : ℤ) - k + 2) ^ 2 * ((N : ℤ) - k + 3)))
  have qO0 : (FO N k : ℚ) = FE (N + 1) k * (((N : ℚ) - k + 1) * ((N : ℚ) - k + 2)) /
      (2 * ((N : ℚ) + 1) * (2 * N - 2 * k + 3)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n3)]
    exact_mod_cast (by linear_combination r0 :
      FO N k * (2 * ((N : ℤ) + 1) * (2 * N - 2 * k + 3)) =
        FE (N + 1) k * (((N : ℤ) - k + 1) * ((N : ℤ) - k + 2)))
  have qF0 : (FE N k : ℚ) = FE (N + 1) k * (((N : ℚ) - k + 1) ^ 2 * ((N : ℚ) - k + 2)) /
      (4 * ((N : ℚ) + 1) * (2 * N + 1) * (2 * N - 2 * k + 3)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n3)]
    exact_mod_cast (by linear_combination -f0 :
      FE N k * (4 * ((N : ℤ) + 1) * (2 * N + 1) * (2 * N - 2 * k + 3)) =
        FE (N + 1) k * (((N : ℤ) - k + 1) ^ 2 * ((N : ℤ) - k + 2)))
  have qy : (FE (N + 2) (k + 1) : ℚ) =
      ((N : ℚ) - k + 2) ^ 2 * ((N : ℚ) - k + 3) * FE (N + 2) k / (2 * ((k : ℚ) + 1) ^ 2 * (2 * N - 2 * k + 5)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n5)]
    exact_mod_cast (by linear_combination fy :
      FE (N + 2) (k + 1) * (2 * ((k : ℤ) + 1) ^ 2 * (2 * N - 2 * k + 5)) =
        ((N : ℤ) - k + 2) ^ 2 * ((N : ℤ) - k + 3) * FE (N + 2) k)
  have n5' : (2 * (N : ℚ) - 2 * ((k + 1 : ℕ) : ℚ) + 5) = 2 * N - 2 * k + 3 := by push_cast; ring
  -- field_simp writes 2N - 2k + c as 2(N - k) + c and needs that form to be nonzero
  have m5 : 2 * ((N : ℚ) - k) + 5 ≠ 0 := by rw [mul_sub]; exact n5
  have m3 : 2 * ((N : ℚ) - k) + 3 ≠ 0 := by rw [mul_sub]; exact n3
  simp only [Gx]
  rw [n5', qO0, qF0, qF1, qO1, qy]
  simp only [cpx]
  push_cast
  field_simp
  ring

lemma SE_ext (n L : ℕ) (hL : n + 1 ≤ L) : (SE n : ℚ) = ∑ k ∈ Finset.range L, (FE n k : ℚ) := by
  rw [SE, Int.cast_sum]
  refine Finset.sum_subset (Finset.range_subset_range.2 hL) (fun k _ hk => ?_)
  rw [Finset.mem_range, not_lt] at hk
  rw [FE, Nat.choose_eq_zero_of_lt (by omega)]
  simp

lemma SO_ext (n L : ℕ) (hL : n + 1 ≤ L) : (SO n : ℚ) = ∑ k ∈ Finset.range L, (FO n k : ℚ) := by
  rw [SO, Int.cast_sum]
  refine Finset.sum_subset (Finset.range_subset_range.2 hL) (fun k _ hk => ?_)
  rw [Finset.mem_range, not_lt] at hk
  rw [FO, Nat.choose_eq_zero_of_lt (by omega)]
  simp

lemma X_eq_sum (N L : ℕ) (hL : N + 2 ≤ L) : (X N : ℚ) = ∑ k ∈ Finset.range L, xk N k := by
  rw [X]
  push_cast
  rw [SE_ext (N + 1) L hL, SE_ext N L (by omega), SO_ext N L (by omega), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rfl

theorem rec_X (N : ℕ) : ((N : ℤ) + 2) ^ 2 * X (N + 1) - 2 * ((N : ℤ) + 1) * (2 * N + 5) * X N = 0 := by
  have g0 : Gx N 0 = 0 := by simp [Gx, cpx]
  have g1 : Gx N (N + 3) = 0 := by
    rw [Gx, FE, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hq : ((N : ℚ) + 2) ^ 2 * X (N + 1) - 2 * ((N : ℚ) + 1) * (2 * N + 5) * X N = 0 := by
    rw [X_eq_sum (N + 1) (N + 3) le_rfl, X_eq_sum N (N + 3) (by omega), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun k _ => certx N k), Finset.sum_range_sub (Gx N), g0, g1,
      sub_zero]
  exact_mod_cast hq

lemma X_zero : X 0 = 0 := by
  decide +kernel

lemma X_eq_zero : ∀ N, X N = 0
  | 0 => X_zero
  | N + 1 => by
    have h := rec_X N
    rw [X_eq_zero N, mul_zero, sub_zero] at h
    have hne : ((N : ℤ) + 2) ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left hne

/-! ### The recurrence -/

/-- Mathar's expression at n = 2N + 6, from the cross relations and the order-2 recurrence of the even terms. -/
lemma mathar_even (N : ℕ) :
    ((2 * (N : ℤ) + 6) + 1) * ((2 * (N : ℤ) + 6) + 2) ^ 2 * SE (N + 3) +
      2 * (7 * (2 * (N : ℤ) + 6) ^ 3 - 17 * (2 * (N : ℤ) + 6) - 6) * SO (N + 2) +
      (-4) * (4 * (2 * (N : ℤ) + 6) - 1) * (4 * (2 * (N : ℤ) + 6) ^ 2 + 9 * (2 * (N : ℤ) + 6) - 12) * SE (N + 2) +
      8 * (-70 * (2 * (N : ℤ) + 6) ^ 3 + 330 * (2 * (N : ℤ) + 6) ^ 2 - 461 * (2 * (N : ℤ) + 6) + 225) * SO (N + 1) +
      48 * ((2 * (N : ℤ) + 6) - 3) * (23 * (2 * (N : ℤ) + 6) ^ 2 - 66 * (2 * (N : ℤ) + 6) + 64) * SE (N + 1) +
      288 * (7 * (2 * (N : ℤ) + 6) - 17) * ((2 * (N : ℤ) + 6) - 3) * ((2 * (N : ℤ) + 6) - 4) * SO N +
      (-3456) * ((2 * (N : ℤ) + 6) - 5) * ((2 * (N : ℤ) + 6) - 3) * ((2 * (N : ℤ) + 6) - 4) * SE N = 0 := by
  have hX0 := X_eq_zero N
  have hX1 := X_eq_zero (N + 1)
  have hX2 := X_eq_zero (N + 2)
  have he0 := e_eq_zero N
  have he1 := e_eq_zero (N + 1)
  simp only [X, e, p0, p1, p2, Nat.add_assoc, Nat.reduceAdd] at hX0 hX1 hX2 he0 he1
  push_cast at hX0 hX1 hX2 he0 he1
  have hD : ((8 * (N : ℤ) ^ 2 + 24 * (N : ℤ) + 19)
      * (8 * ((N : ℤ) + 1) ^ 2 + 24 * ((N : ℤ) + 1) + 19)
      * (8 * ((N : ℤ) + 2) ^ 2 + 24 * ((N : ℤ) + 2) + 19) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.1 ?_).resolve_left hD
  linear_combination (-218116800 - 780124608 * (N : ℤ) - 1153239552 * (N : ℤ) ^ 2 - 916630272 * (N : ℤ) ^ 3
    - 424341504 * (N : ℤ) ^ 4 - 114720768 * (N : ℤ) ^ 5 - 16809984 * (N : ℤ) ^ 6
    - 1032192 * (N : ℤ) ^ 7) * hX0 + (86992488 + 281312976 * (N : ℤ) + 385311424 * (N : ℤ) ^ 2
    + 289065088 * (N : ℤ) ^ 3 + 128046592 * (N : ℤ) ^ 4 + 33455104 * (N : ℤ) ^ 5 + 4771840 * (N : ℤ) ^ 6
    + 286720 * (N : ℤ) ^ 7) * hX1 + (-2720952 - 8435436 * (N : ℤ) - 11109616 * (N : ℤ) ^ 2
    - 8039216 * (N : ℤ) ^ 3 - 3447552 * (N : ℤ) ^ 4 - 875520 * (N : ℤ) ^ 5 - 121856 * (N : ℤ) ^ 6
    - 7168 * (N : ℤ) ^ 7) * hX2 + (-123552 - 155424 * (N : ℤ) - 77376 * (N : ℤ) ^ 2 - 17664 * (N : ℤ) ^ 3
    - 1536 * (N : ℤ) ^ 4) * he0 + (35340 + 66528 * (N : ℤ) + 45872 * (N : ℤ) ^ 2 + 13440 * (N : ℤ) ^ 3
    + 1408 * (N : ℤ) ^ 4) * he1

/-- Mathar's expression at n = 2N + 7, from the cross relations and the order-2 recurrence of the even terms. -/
lemma mathar_odd (N : ℕ) :
    ((2 * (N : ℤ) + 7) + 1) * ((2 * (N : ℤ) + 7) + 2) ^ 2 * SO (N + 3) +
      2 * (7 * (2 * (N : ℤ) + 7) ^ 3 - 17 * (2 * (N : ℤ) + 7) - 6) * SE (N + 3) +
      (-4) * (4 * (2 * (N : ℤ) + 7) - 1) * (4 * (2 * (N : ℤ) + 7) ^ 2 + 9 * (2 * (N : ℤ) + 7) - 12) * SO (N + 2) +
      8 * (-70 * (2 * (N : ℤ) + 7) ^ 3 + 330 * (2 * (N : ℤ) + 7) ^ 2 - 461 * (2 * (N : ℤ) + 7) + 225) * SE (N + 2) +
      48 * ((2 * (N : ℤ) + 7) - 3) * (23 * (2 * (N : ℤ) + 7) ^ 2 - 66 * (2 * (N : ℤ) + 7) + 64) * SO (N + 1) +
      288 * (7 * (2 * (N : ℤ) + 7) - 17) * ((2 * (N : ℤ) + 7) - 3) * ((2 * (N : ℤ) + 7) - 4) * SE (N + 1) +
      (-3456) * ((2 * (N : ℤ) + 7) - 5) * ((2 * (N : ℤ) + 7) - 3) * ((2 * (N : ℤ) + 7) - 4) * SO N = 0 := by
  have hX0 := X_eq_zero N
  have hX1 := X_eq_zero (N + 1)
  have hX2 := X_eq_zero (N + 2)
  have hX3 := X_eq_zero (N + 3)
  have he0 := e_eq_zero N
  have he1 := e_eq_zero (N + 1)
  have he2 := e_eq_zero (N + 2)
  simp only [X, e, p0, p1, p2, Nat.add_assoc, Nat.reduceAdd] at hX0 hX1 hX2 hX3 he0 he1 he2
  push_cast at hX0 hX1 hX2 hX3 he0 he1 he2
  have hD : ((8 * (N : ℤ) ^ 2 + 24 * (N : ℤ) + 19)
      * (8 * ((N : ℤ) + 1) ^ 2 + 24 * ((N : ℤ) + 1) + 19) * (8 * ((N : ℤ) + 2) ^ 2 + 24 * ((N : ℤ) + 2) + 19)
      * (8 * ((N : ℤ) + 3) ^ 2 + 24 * ((N : ℤ) + 3) + 19) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.1 ?_).resolve_left hD
  linear_combination (68261833728 + 270204553728 * (N : ℤ) + 457948131840 * (N : ℤ) ^ 2
    + 437880480768 * (N : ℤ) ^ 3 + 261155155968 * (N : ℤ) ^ 4 + 101011857408 * (N : ℤ) ^ 5
    + 25392807936 * (N : ℤ) ^ 6 + 4007854080 * (N : ℤ) ^ 7 + 360972288 * (N : ℤ) ^ 8
    + 14155776 * (N : ℤ) ^ 9) * hX0 + (-42914608704 - 149036608800 * (N : ℤ) - 226613752320 * (N : ℤ) ^ 2
    - 197709128832 * (N : ℤ) ^ 3 - 109003502592 * (N : ℤ) ^ 4 - 39382520832 * (N : ℤ) ^ 5
    - 9327034368 * (N : ℤ) ^ 6 - 1396924416 * (N : ℤ) ^ 7 - 120127488 * (N : ℤ) ^ 8
    - 4521984 * (N : ℤ) ^ 9) * hX1 + (4213394172 + 13953925128 * (N : ℤ) + 20184146336 * (N : ℤ) ^ 2
    + 16706501952 * (N : ℤ) ^ 3 + 8714094848 * (N : ℤ) ^ 4 + 2970076672 * (N : ℤ) ^ 5
    + 661624832 * (N : ℤ) ^ 6 + 92925952 * (N : ℤ) ^ 7 + 7471104 * (N : ℤ) ^ 8 + 262144 * (N : ℤ) ^ 9) * hX2 +
    (-62163288 - 205609590 * (N : ℤ) - 297312552 * (N : ℤ) ^ 2 - 246328008 * (N : ℤ) ^ 3
    - 128837248 * (N : ℤ) ^ 4 - 44131648 * (N : ℤ) ^ 5 - 9906688 * (N : ℤ) ^ 6 - 1406464 * (N : ℤ) ^ 7
    - 114688 * (N : ℤ) ^ 8 - 4096 * (N : ℤ) ^ 9) * hX3 + (-74359296 - 186446592 * (N : ℤ)
    - 177778944 * (N : ℤ) ^ 2 - 84529152 * (N : ℤ) ^ 3 - 21491712 * (N : ℤ) ^ 4 - 2801664 * (N : ℤ) ^ 5
    - 147456 * (N : ℤ) ^ 6) * he0 + (23487648 + 55255984 * (N : ℤ) + 52560416 * (N : ℤ) ^ 2
    + 25688320 * (N : ℤ) ^ 3 + 6804992 * (N : ℤ) ^ 4 + 928768 * (N : ℤ) ^ 5 + 51200 * (N : ℤ) ^ 6) * he1 +
    (156978 + 391176 * (N : ℤ) + 396840 * (N : ℤ) ^ 2 + 208256 * (N : ℤ) ^ 3 + 59392 * (N : ℤ) ^ 4
    + 8704 * (N : ℤ) ^ 5 + 512 * (N : ℤ) ^ 6) * he2

/-- Mathar's recurrence, for every n ≥ 6. -/
theorem conjecture :
    ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 1) * ((n : ℤ) + 2) ^ 2 * (a n : ℤ) + 2 * (7 * (n : ℤ) ^ 3 - 17 * (n : ℤ) - 6) * (a (n - 1) : ℤ) -
      4 * (4 * (n : ℤ) - 1) * (4 * (n : ℤ) ^ 2 + 9 * (n : ℤ) - 12) * (a (n - 2) : ℤ) +
      8 * (-70 * (n : ℤ) ^ 3 + 330 * (n : ℤ) ^ 2 - 461 * (n : ℤ) + 225) * (a (n - 3) : ℤ) +
      48 * ((n : ℤ) - 3) * (23 * (n : ℤ) ^ 2 - 66 * (n : ℤ) + 64) * (a (n - 4) : ℤ) +
      288 * (7 * (n : ℤ) - 17) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 5) : ℤ) -
      3456 * ((n : ℤ) - 5) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 6) : ℤ) = 0 := by
  intro n hn
  obtain ⟨N, rfl | rfl⟩ : ∃ N, n = 2 * N + 6 ∨ n = 2 * N + 7 := ⟨(n - 6) / 2, by omega⟩
  · rw [show 2 * N + 6 - 1 = 2 * (N + 2) + 1 by omega, show 2 * N + 6 - 2 = 2 * (N + 2) by omega,
      show 2 * N + 6 - 3 = 2 * (N + 1) + 1 by omega, show 2 * N + 6 - 4 = 2 * (N + 1) by omega,
      show 2 * N + 6 - 5 = 2 * N + 1 by omega, show 2 * N + 6 - 6 = 2 * N by omega,
      show 2 * N + 6 = 2 * (N + 3) by ring, a_even, a_even, a_even, a_even, a_odd, a_odd, a_odd]
    push_cast
    linear_combination mathar_even N
  · rw [show 2 * N + 7 - 1 = 2 * (N + 3) by omega, show 2 * N + 7 - 2 = 2 * (N + 2) + 1 by omega,
      show 2 * N + 7 - 3 = 2 * (N + 2) by omega, show 2 * N + 7 - 4 = 2 * (N + 1) + 1 by omega,
      show 2 * N + 7 - 5 = 2 * (N + 1) by omega, show 2 * N + 7 - 6 = 2 * N + 1 by omega,
      show 2 * N + 7 = 2 * (N + 3) + 1 by ring, a_even, a_even, a_even, a_odd, a_odd, a_odd, a_odd]
    push_cast
    linear_combination mathar_odd N

/-- Controls: the entry's data a(0..25). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 8 ∧ a 3 = 30 ∧ a 4 = 138 ∧ a 5 = 620 ∧ a 6 = 3060 ∧ a 7 = 14910 ∧ a 8
    = 76650 ∧ a 9 = 390852 ∧ a 10 = 2063376 ∧ a 11 = 10832052 ∧ a 12 = 58264668 ∧ a 13 = 312123240 ∧
    a 14 = 1702423008 ∧ a 15 = 9256786110 ∧ a 16 = 51036229530 ∧ a 17 = 280696824980 ∧ a 18 =
    1560925457520 ∧ a 19 = 8663089672380 ∧ a 20 = 48512836025940 ∧ a 21 = 271229902496280 ∧ a 22 =
    1527733861191720 ∧ a 23 = 8593482390429300 ∧ a 24 = 48642125421855420 ∧ a 25 =
    275014629509319000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
  ?_, ?_, ?_, ?_⟩
  · rw [← Int.natCast_inj, show (0 : ℕ) = 2 * 0 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (1 : ℕ) = 2 * 0 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (2 : ℕ) = 2 * 1 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (3 : ℕ) = 2 * 1 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (4 : ℕ) = 2 * 2 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (5 : ℕ) = 2 * 2 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (6 : ℕ) = 2 * 3 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (7 : ℕ) = 2 * 3 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (8 : ℕ) = 2 * 4 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (9 : ℕ) = 2 * 4 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (10 : ℕ) = 2 * 5 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (11 : ℕ) = 2 * 5 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (12 : ℕ) = 2 * 6 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (13 : ℕ) = 2 * 6 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (14 : ℕ) = 2 * 7 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (15 : ℕ) = 2 * 7 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (16 : ℕ) = 2 * 8 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (17 : ℕ) = 2 * 8 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (18 : ℕ) = 2 * 9 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (19 : ℕ) = 2 * 9 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (20 : ℕ) = 2 * 10 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (21 : ℕ) = 2 * 10 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (22 : ℕ) = 2 * 11 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (23 : ℕ) = 2 * 11 + 1 from rfl, a_odd]
    decide +kernel
  · rw [← Int.natCast_inj, show (24 : ℕ) = 2 * 12 from rfl, a_even]
    decide +kernel
  · rw [← Int.natCast_inj, show (25 : ℕ) = 2 * 12 + 1 from rfl, a_odd]
    decide +kernel

end OMA.S_oeis_a302187

theorem OMA.solution : type_of% @OMA.S_oeis_a302187.main :=
  OMA.S_oeis_a302187.conjecture
