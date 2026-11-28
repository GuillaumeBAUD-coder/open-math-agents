import OMAStatements.S_oeis_a302182

namespace OMA.S_oeis_a302182




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

/-- The walks of N steps from the point (h, y, z) that keep x ≥ 0 and z ≥ 0 and end with x = 0 and y = 0. -/
def cnt (N : ℕ) (h y z : ℤ) : ℕ :=
  (Finset.univ.filter (fun w : Fin N → Fin 6 =>
    (∀ t ≤ N, 0 ≤ h + (pt w t).1 ∧ 0 ≤ z + (pt w t).2.2) ∧ h + (pt w N).1 = 0 ∧ y + (pt w N).2.1 = 0)).card

lemma a_eq_cnt (n : ℕ) : a n = cnt n 0 0 0 := by
  simp only [a, cnt, zero_add]

lemma cnt_neg (N : ℕ) {h z : ℤ} (y : ℤ) (hh : h < 0 ∨ z < 0) : cnt N h y z = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hw
  have h0 := hw.1 0 (Nat.zero_le _)
  rw [pt_zero] at h0
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero] at h0
  omega

lemma cond_cons {N : ℕ} (c : Fin 6) (w : Fin N → Fin 6) (h y z : ℤ) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    ((∀ t ≤ N + 1, 0 ≤ h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).1 ∧
        0 ≤ z + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).2.2) ∧
      h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).1 = 0 ∧
      y + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).2.1 = 0) ↔
    ((∀ t ≤ N, 0 ≤ (h + (step c).1) + (pt w t).1 ∧ 0 ≤ (z + (step c).2.2) + (pt w t).2.2) ∧
      (h + (step c).1) + (pt w N).1 = 0 ∧ (y + (step c).2.1) + (pt w N).2.1 = 0) := by
  rw [pt_cons]
  simp only [Prod.fst_add, Prod.snd_add, ← add_assoc]
  refine and_congr ⟨fun H t ht => ?_, fun H t ht => ?_⟩ Iff.rfl
  · have := H (t + 1) (by omega)
    simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc] at this
    exact this
  · rcases t with _ | t
    · simp only [pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
      exact ⟨hh, hz⟩
    · simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc]
      exact H t (by omega)

lemma cnt_succ_sum (N : ℕ) (h y z : ℤ) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    cnt (N + 1) h y z = ∑ c : Fin 6, cnt N (h + (step c).1) (y + (step c).2.1) (z + (step c).2.2) := by
  rw [cnt, Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin 6)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [cnt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact if_congr (cond_cons c w h y z hh hz) rfl rfl

lemma cnt_succ (N : ℕ) (h y z : ℤ) (hh : 0 ≤ h) (hz : 0 ≤ z) :
    (cnt (N + 1) h y z : ℤ) = cnt N (h + 1) y z + cnt N (h - 1) y z + cnt N h (y + 1) z + cnt N h (y - 1) z +
      cnt N h y (z + 1) + cnt N h y (z - 1) := by
  rw [cnt_succ_sum N h y z hh hz, Fin.sum_univ_six]
  simp [step]
  ring_nf

/-! ### The z-steps: a ±1 walk that stays ≥ 0, by reflection and a cumulative count -/

/-- The ±1 walks of m steps whose sum is at least -t (by recursion on m). -/
def Cum1 : ℕ → ℤ → ℤ
  | 0, t => if 0 ≤ t then 1 else 0
  | m + 1, t => Cum1 m (t + 1) + Cum1 m (t - 1)

lemma Cum1_diff : ∀ (m : ℕ) (t : ℤ), Cum1 m t - Cum1 m (t - 1) = bin1 m t
  | 0, t => by
    simp only [Cum1, bin1]
    split_ifs <;> omega
  | m + 1, t => by
    have h1 := Cum1_diff m (t + 1)
    have h3 := Cum1_diff m (t - 1)
    rw [show t + 1 - 1 = t by ring] at h1
    rw [bin1]
    simp only [Cum1]
    rw [show t - 1 + 1 = t by ring]
    linear_combination h1 + h3

/-- The ±1 walks of m steps from z that stay ≥ 0, by reflection in -1. -/
def Mz (m : ℕ) (z : ℤ) : ℤ := Cum1 m z - Cum1 m (-2 - z)

lemma Mz_succ (m : ℕ) (z : ℤ) : Mz (m + 1) z = Mz m (z + 1) + Mz m (z - 1) := by
  simp only [Mz, Cum1]
  rw [show -2 - z + 1 = -1 - z by ring, show -2 - z - 1 = -3 - z by ring, show -2 - (z + 1) = -3 - z by ring,
    show -2 - (z - 1) = -1 - z by ring]
  ring

lemma Mz_neg_one (m : ℕ) : Mz m (-1) = 0 := by
  rw [Mz, show (-2 : ℤ) - -1 = -1 by norm_num, sub_self]

lemma Mz_zero (m : ℕ) : Mz m 0 = bin1 m 0 + bin1 m (-1) := by
  have h0 := Cum1_diff m 0
  have h1 := Cum1_diff m (-1)
  rw [show (0 : ℤ) - 1 = -1 by norm_num] at h0
  rw [show (-1 : ℤ) - 1 = -2 by norm_num] at h1
  rw [Mz, show (-2 : ℤ) - 0 = -2 by norm_num]
  linear_combination h0 + h1

/-! ### The (x, y)-steps and the z-steps interleaved -/

/-- Tz N f z = Sum_k C(N, k) f(k) Mz(N - k, z). -/
def Tz (N : ℕ) (f : ℕ → ℤ) (z : ℤ) : ℤ := ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * Mz (N - k) z

lemma Tz_succ (N : ℕ) (f : ℕ → ℤ) (z : ℤ) :
    Tz (N + 1) f z = Tz N (fun k => f (k + 1)) z + Tz N f (z + 1) + Tz N f (z - 1) := by
  have h1 : Tz (N + 1) f z = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * Mz (N - k) z +
      ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * Mz (N - k) z + f 0 * Mz (N + 1) z := by
    rw [Tz, Finset.sum_range_succ', ← Finset.sum_add_distrib]
    simp only [Nat.choose_succ_succ', Nat.add_sub_add_right, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_add,
      Nat.cast_one, one_mul, add_mul]
  have h2 : Tz N f (z + 1) + Tz N f (z - 1) =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * Mz (N - k) z + f 0 * Mz (N + 1) z := by
    rw [Tz, Tz, ← Finset.sum_add_distrib]
    have e : ∀ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * Mz (N - k) (z + 1) +
        (N.choose k : ℤ) * f k * Mz (N - k) (z - 1) = (N.choose k : ℤ) * f k * Mz (N + 1 - k) z := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show N + 1 - k = N - k + 1 by omega, Mz_succ]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [show N + 1 - (k + 1) = N - k by omega]
  have h3 : ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * Mz (N - k) z =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * Mz (N - k) z := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero]
  have h4 : Tz N (fun k => f (k + 1)) z =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * Mz (N - k) z := rfl
  rw [h1, h3]
  linarith [h2, h4]

lemma cnt_zero (h y z : ℤ) (hh : -1 ≤ h) (hz : -1 ≤ z) : (cnt 0 h y z : ℤ) = AB 0 h y * Mz 0 z := by
  have hc : cnt 0 h y z = if h = 0 ∧ y = 0 ∧ 0 ≤ z then 1 else 0 := by
    rw [cnt, Finset.card_filter, Fintype.sum_unique]
    simp only [nonpos_iff_eq_zero, forall_eq, pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
    by_cases h0 : h = 0 <;> by_cases y0 : y = 0 <;> by_cases z0 : 0 ≤ z <;> simp [h0, y0, z0]
  rw [hc]
  simp only [AB, P, bin1, Mz, Cum1]
  split_ifs <;> omega

/-- The count from any start with x, z ≥ -1. -/
theorem cnt_eq (N : ℕ) : ∀ h y z : ℤ, -1 ≤ h → -1 ≤ z → (cnt N h y z : ℤ) = Tz N (fun k => AB k h y) z := by
  induction N with
  | zero =>
    intro h y z hh hz
    rw [cnt_zero h y z hh hz]
    simp [Tz]
  | succ N ih =>
    intro h y z hh hz
    rcases eq_or_lt_of_le hh with e | hh'
    · rw [← e, cnt_neg _ _ (Or.inl (by norm_num)), Nat.cast_zero]
      simp [Tz, AB_neg_one]
    rcases eq_or_lt_of_le hz with e | hz'
    · rw [← e, cnt_neg _ _ (Or.inr (by norm_num)), Nat.cast_zero]
      simp [Tz, Mz_neg_one]
    have h0 : 0 ≤ h := by omega
    have z0 : 0 ≤ z := by omega
    have hs : Tz N (fun k => AB (k + 1) h y) z = Tz N (fun k => AB k (h + 1) y) z +
        Tz N (fun k => AB k (h - 1) y) z + Tz N (fun k => AB k h (y + 1)) z + Tz N (fun k => AB k h (y - 1)) z := by
      simp only [Tz, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [AB_succ]; ring)
    rw [cnt_succ N h y z h0 z0, ih (h + 1) y z (by omega) hz, ih (h - 1) y z (by omega) hz, ih h (y + 1) z hh hz,
      ih h (y - 1) z hh hz, ih h y (z + 1) hh (by omega), ih h y (z - 1) hh (by omega), Tz_succ, hs]

/-! ### The sum -/

/-- The summand: 2k steps on the x and y axes (a walk of type ab back to the origin) and 2n - 2k
z-steps (a ±1 walk back to 0), interleaved. -/
def F (n k : ℕ) : ℤ := ((2 * n).choose (2 * k) : ℤ) * w k * ((2 * n - 2 * k).choose (n - k) : ℤ)

/-- The sum over k. -/
def S (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), F n k

/-! ### Shift relations -/

lemma w_mul (i : ℕ) : w i * ((i : ℤ) + 1) ^ 2 = (2 * i + 1) * ((2 * i).choose i : ℤ) ^ 2 := by
  have hc := Nat.choose_succ_right_eq (2 * i) i
  rw [show 2 * i - i = i by omega] at hc
  have hc' : ((2 * i).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((2 * i).choose i : ℤ) * i := by
    exact_mod_cast hc
  simp only [w]
  linear_combination (-(((2 * i).choose (i + 1) : ℤ) * ((i : ℤ) + 1) + ((2 * i).choose i : ℤ) * i)) * hc'

lemma w_succ (i : ℕ) : w (i + 1) * ((i : ℤ) + 2) ^ 2 = 4 * (2 * i + 1) * (2 * i + 3) * w i := by
  have h1 := w_mul (i + 1)
  have h0 := w_mul i
  have hb := Nat.succ_mul_centralBinom_succ i
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hb
  have hb' : ((i : ℤ) + 1) * ((2 * (i + 1)).choose (i + 1) : ℤ) = 2 * (2 * i + 1) * ((2 * i).choose i : ℤ) := by
    exact_mod_cast hb
  push_cast at h1
  have key : (w (i + 1) * ((i : ℤ) + 2) ^ 2 - 4 * (2 * i + 1) * (2 * i + 3) * w i) * ((i : ℤ) + 1) ^ 2 = 0 := by
    linear_combination ((i : ℤ) + 1) ^ 2 * h1 - 4 * (2 * (i : ℤ) + 1) * (2 * i + 3) * h0 +
      (2 * (i : ℤ) + 3) * (((i : ℤ) + 1) * ((2 * (i + 1)).choose (i + 1) : ℤ) + 2 * (2 * i + 1) *
        ((2 * i).choose i : ℤ)) * hb'
  have hne : ((i : ℤ) + 1) ^ 2 ≠ 0 := by positivity
  linear_combination (mul_eq_zero.1 key).resolve_right hne

lemma cb_succ (m : ℕ) : ((2 * m + 2).choose (m + 1) : ℤ) * ((m : ℤ) + 1) = 2 * (2 * m + 1) * ((2 * m).choose m : ℤ) := by
  have hb := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose,
    show 2 * (m + 1) = 2 * m + 2 by ring] at hb
  have e : ((m : ℤ) + 1) * ((2 * m + 2).choose (m + 1) : ℤ) = 2 * (2 * m + 1) * ((2 * m).choose m : ℤ) := by
    exact_mod_cast hb
  linear_combination e

/-- One more step in n. -/
lemma Fn (n k : ℕ) : F (n + 1) k * ((n : ℤ) + 1 - k) ^ 2 = 2 * ((n : ℤ) + 1) * (2 * n + 1) * F n k := by
  rcases Nat.lt_or_ge n k with h | h
  · have h0 : F n k = 0 := by
      rw [F, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rcases Nat.eq_or_lt_of_le h with e | e
    · subst e
      rw [h0]
      push_cast
      ring
    · have h1 : F (n + 1) k = 0 := by
        rw [F, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [h0, h1]
      ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
    simp only [F]
    rw [show 2 * (k + m + 1) - 2 * k = 2 * m + 2 by omega, show k + m + 1 - k = m + 1 by omega,
      show 2 * (k + m) - 2 * k = 2 * m by omega, show k + m - k = m by omega]
    have hA1 := Nat.choose_mul_succ_eq (2 * (k + m)) (2 * k)
    have hA2 := Nat.choose_mul_succ_eq (2 * (k + m) + 1) (2 * k)
    rw [show 2 * (k + m) + 1 - 2 * k = 2 * m + 1 by omega] at hA1
    rw [show 2 * (k + m) + 1 + 1 - 2 * k = 2 * m + 2 by omega,
      show 2 * (k + m) + 1 + 1 = 2 * (k + m + 1) by ring] at hA2
    have eA1 : ((2 * (k + m)).choose (2 * k) : ℤ) * (2 * ((k : ℤ) + m) + 1) =
        ((2 * (k + m) + 1).choose (2 * k) : ℤ) * (2 * m + 1) := by
      exact_mod_cast hA1
    have eA2 : ((2 * (k + m) + 1).choose (2 * k) : ℤ) * (2 * ((k : ℤ) + m) + 2) =
        ((2 * (k + m + 1)).choose (2 * k) : ℤ) * (2 * m + 2) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) hA2
      push_cast at e ⊢
      linear_combination e
    have eB := cb_succ m
    push_cast
    linear_combination (w k * ((m : ℤ) + 1) * ((2 * (k + m + 1)).choose (2 * k) : ℤ)) * eB -
      ((2 * (m : ℤ) + 1) * w k * ((2 * m).choose m : ℤ)) * eA2 -
      (2 * ((k : ℤ) + m + 1) * w k * ((2 * m).choose m : ℤ)) * eA1

/-- One more step in k. -/
lemma Fk (n k : ℕ) : F n (k + 1) * ((2 * (k : ℤ) + 2) * ((k : ℤ) + 2) ^ 2) =
    4 * (2 * k + 3) * ((n : ℤ) - k) ^ 2 * F n k := by
  rcases Nat.lt_or_ge k n with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - k - 1, by omega⟩
    simp only [F]
    rw [show 2 * (k + 1 + m) - 2 * (k + 1) = 2 * m by omega, show k + 1 + m - (k + 1) = m by omega,
      show 2 * (k + 1 + m) - 2 * k = 2 * m + 2 by omega, show k + 1 + m - k = m + 1 by omega]
    have hC1 := Nat.choose_succ_right_eq (2 * (k + 1 + m)) (2 * k)
    have hC2 := Nat.choose_succ_right_eq (2 * (k + 1 + m)) (2 * k + 1)
    rw [show 2 * (k + 1 + m) - 2 * k = 2 * m + 2 by omega] at hC1
    rw [show 2 * (k + 1 + m) - (2 * k + 1) = 2 * m + 1 by omega, show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at hC2
    have eC1 : ((2 * (k + 1 + m)).choose (2 * k + 1) : ℤ) * (2 * k + 1) =
        ((2 * (k + 1 + m)).choose (2 * k) : ℤ) * (2 * m + 2) := by
      exact_mod_cast hC1
    have eC2 : ((2 * (k + 1 + m)).choose (2 * (k + 1)) : ℤ) * (2 * k + 2) =
        ((2 * (k + 1 + m)).choose (2 * k + 1) : ℤ) * (2 * m + 1) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) hC2
      push_cast at e ⊢
      linear_combination e
    have ew := w_succ k
    have eB := cb_succ m
    push_cast
    have key : (((2 * (k + 1 + m)).choose (2 * (k + 1)) : ℤ) * w (k + 1) * ((2 * m).choose m : ℤ) *
        ((2 * (k : ℤ) + 2) * ((k : ℤ) + 2) ^ 2) - 4 * (2 * (k : ℤ) + 3) * ((k : ℤ) + 1 + m - k) ^ 2 *
        (((2 * (k + 1 + m)).choose (2 * k) : ℤ) * w k * ((2 * m + 2).choose (m + 1) : ℤ))) *
        (2 * (k : ℤ) + 1) = 0 := by
      linear_combination (w (k + 1) * ((2 * m).choose m : ℤ) * ((k : ℤ) + 2) ^ 2 * (2 * (k : ℤ) + 1)) * eC2 +
        (((2 * m).choose m : ℤ) * (2 * (k : ℤ) + 1) * ((2 * (k + 1 + m)).choose (2 * k + 1) : ℤ) *
          (2 * (m : ℤ) + 1)) * ew -
        (2 * (2 * (k : ℤ) + 3) * (2 * (k : ℤ) + 1) ^ 2 * w k * ((2 * (k + 1 + m)).choose (2 * k + 1) : ℤ)) * eB +
        (2 * (2 * (k : ℤ) + 3) * ((m : ℤ) + 1) * (2 * (k : ℤ) + 1) * w k * ((2 * m + 2).choose (m + 1) : ℤ)) * eC1
    have hne : (2 * (k : ℤ) + 1) ≠ 0 := by positivity
    linear_combination (mul_eq_zero.1 key).resolve_right hne
  · rcases Nat.eq_or_lt_of_le h with e | e
    · subst e
      have h1 : F n (n + 1) = 0 := by
        rw [F, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [h1]
      ring
    · have h0 : F n k = 0 := by
        rw [F, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      have h1 : F n (k + 1) = 0 := by
        rw [F, Nat.choose_eq_zero_of_lt (by omega)]
        simp
      rw [h0, h1]
      ring

/-! ### Mathar's operator, an order-3 telescoper, and its certificate -/

/-- Mathar's coefficients at n = m + 2, for a(m), a(m+1), a(m+2). -/
def l0 (m : ℕ) : ℤ := 36 * ((m : ℤ) + 2) * (2 * m + 3) * (2 * m + 1)
def l1 (m : ℕ) : ℤ := -2 * (2 * (m : ℤ) + 3) * (10 * ((m : ℤ) + 2) ^ 2 + 10 * ((m : ℤ) + 2) + 3)
def l2 (m : ℕ) : ℤ := ((m : ℤ) + 3) ^ 3

/-- The telescoper (m+3)^2 L(m+1) - 2(m+1)(2m+7) L(m), with L Mathar's operator. -/
def t0 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 1) * (2 * m + 7) * l0 m
def t1 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 1) * (2 * m + 7) * l1 m + ((m : ℤ) + 3) ^ 2 * l0 (m + 1)
def t2 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 1) * (2 * m + 7) * l2 m + ((m : ℤ) + 3) ^ 2 * l1 (m + 1)
def t3 (m : ℕ) : ℤ := ((m : ℤ) + 3) ^ 2 * l2 (m + 1)

/-- The certificate: G(m, k) = cp(m, k) F(m + 3, k), cp a polynomial in k. -/
def cp (m k : ℕ) : ℚ :=
  (-(16 * (m : ℚ) ^ 2 + 100 * m + 153) * ((m : ℚ) + 3) * (k : ℚ) ^ 2 -
      2 * (16 * (m : ℚ) ^ 3 + 138 * m ^ 2 + 390 * m + 361) * (k : ℚ) ^ 3 -
      (16 * (m : ℚ) ^ 3 + 108 * m ^ 2 + 207 * m + 88) * (k : ℚ) ^ 4 +
      2 * (2 * (m : ℚ) + 7) * (5 * m + 11) * (k : ℚ) ^ 5 - 3 * (2 * (m : ℚ) + 7) * (k : ℚ) ^ 6) /
    ((2 * (m : ℚ) + 5) * ((m : ℚ) + 3))

def G (m k : ℕ) : ℚ := cp m k * F (m + 3) k

/-- The certificate identity, term by term, for every k. -/
lemma cert (m k : ℕ) :
    (t0 m : ℚ) * F m k + t1 m * F (m + 1) k + t2 m * F (m + 2) k + t3 m * F (m + 3) k = G m (k + 1) - G m k := by
  have e2 := Fn (m + 2) k
  have e1 := Fn (m + 1) k
  have e0 := Fn m k
  have ey := Fk (m + 3) k
  rw [show m + 2 + 1 = m + 3 from rfl] at e2
  rw [show m + 1 + 1 = m + 2 from rfl] at e1
  push_cast at e2 e1 e0 ey
  have q2 : (F (m + 2) k : ℚ) = F (m + 3) k * ((m : ℚ) + 3 - k) ^ 2 / (2 * ((m : ℚ) + 3) * (2 * m + 5)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination -e2 :
      F (m + 2) k * (2 * ((m : ℤ) + 3) * (2 * m + 5)) = F (m + 3) k * ((m : ℤ) + 3 - k) ^ 2)
  have q1 : (F (m + 1) k : ℚ) = F (m + 2) k * ((m : ℚ) + 2 - k) ^ 2 / (2 * ((m : ℚ) + 2) * (2 * m + 3)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination -e1 :
      F (m + 1) k * (2 * ((m : ℤ) + 2) * (2 * m + 3)) = F (m + 2) k * ((m : ℤ) + 2 - k) ^ 2)
  have q0 : (F m k : ℚ) = F (m + 1) k * ((m : ℚ) + 1 - k) ^ 2 / (2 * ((m : ℚ) + 1) * (2 * m + 1)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination -e0 :
      F m k * (2 * ((m : ℤ) + 1) * (2 * m + 1)) = F (m + 1) k * ((m : ℤ) + 1 - k) ^ 2)
  have qy : (F (m + 3) (k + 1) : ℚ) =
      4 * (2 * k + 3) * ((m : ℚ) + 3 - k) ^ 2 * F (m + 3) k / ((2 * (k : ℚ) + 2) * ((k : ℚ) + 2) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination ey :
      F (m + 3) (k + 1) * ((2 * (k : ℤ) + 2) * ((k : ℤ) + 2) ^ 2) =
        4 * (2 * k + 3) * ((m : ℤ) + 3 - k) ^ 2 * F (m + 3) k)
  simp only [G, cp]
  rw [q0, q1, q2, qy]
  simp only [t0, t1, t2, t3, l0, l1, l2]
  push_cast
  field_simp
  ring

/-- The telescoper annihilates the sum. -/
theorem rec_T (m : ℕ) : t0 m * S m + t1 m * S (m + 1) + t2 m * S (m + 2) + t3 m * S (m + 3) = 0 := by
  have ext : ∀ n, n ≤ m + 3 → (S n : ℚ) = ∑ k ∈ Finset.range (m + 4), (F n k : ℚ) := by
    intro n hn
    rw [S, Int.cast_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun k _ hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have g0 : G m 0 = 0 := by simp [G, cp]
  have g1 : G m (m + 4) = 0 := by
    rw [G, F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hq : (t0 m : ℚ) * S m + t1 m * S (m + 1) + t2 m * S (m + 2) + t3 m * S (m + 3) = 0 := by
    rw [ext m (by omega), ext (m + 1) (by omega), ext (m + 2) (by omega), ext (m + 3) le_rfl,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => cert m k),
      Finset.sum_range_sub (G m), g0, g1, sub_zero]
  exact_mod_cast hq

/-! ### From the telescoper to Mathar's recurrence -/

/-- Mathar's expression at n = m + 2. -/
def b (m : ℕ) : ℤ := l0 m * S m + l1 m * S (m + 1) + l2 m * S (m + 2)

lemma b_succ (m : ℕ) : ((m : ℤ) + 3) ^ 2 * b (m + 1) = 2 * ((m : ℤ) + 1) * (2 * m + 7) * b m := by
  have h := rec_T m
  simp only [b, t0, t1, t2, t3] at h ⊢
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl]
  linear_combination h

lemma b_zero : b 0 = 0 := by
  decide +kernel

lemma b_eq_zero : ∀ m, b m = 0
  | 0 => b_zero
  | m + 1 => by
    have h := b_succ m
    rw [b_eq_zero m, mul_zero] at h
    have hne : ((m : ℤ) + 3) ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left hne

/-! ### The even and the odd terms -/

/-- The odd terms: 2t steps on the x and y axes (a walk of type ab back to the origin) and 2N + 1 - 2t z-steps
that stay ≥ 0 (C(2M+1, M+1) of them, M = N - t), interleaved. For the even terms the z-steps that stay ≥ 0
are as many as those that return to 0, C(2M, M), so the even terms are the sums S of the walks of type abb. -/
def FO (N t : ℕ) : ℤ := ((2 * N + 1).choose (2 * t) : ℤ) * w t * ((2 * (N - t) + 1).choose (N - t + 1) : ℤ)

/-- The sum over t. -/
def SO (N : ℕ) : ℤ := ∑ t ∈ Finset.range (N + 1), FO N t

lemma bin1_even_zero (M : ℕ) : bin1 (2 * M) 0 = ((2 * M).choose M : ℤ) := by
  have := bin1_choose (2 * M) M
  rwa [show ((2 * M : ℕ) : ℤ) - 2 * (M : ℤ) = 0 by push_cast; ring] at this

lemma bin1_even_neg_one (M : ℕ) : bin1 (2 * M) (-1) = 0 := by
  have := bin1_odd (2 * M) M
  rwa [show ((2 * M : ℕ) : ℤ) - 2 * (M : ℤ) - 1 = -1 by push_cast; ring] at this

lemma bin1_odd_zero (M : ℕ) : bin1 (2 * M + 1) 0 = 0 := by
  have := bin1_odd (2 * M + 1) M
  rwa [show ((2 * M + 1 : ℕ) : ℤ) - 2 * (M : ℤ) - 1 = 0 by push_cast; ring] at this

lemma bin1_odd_neg_one (M : ℕ) : bin1 (2 * M + 1) (-1) = ((2 * M + 1).choose (M + 1) : ℤ) := by
  have := bin1_choose (2 * M + 1) (M + 1)
  rwa [show ((2 * M + 1 : ℕ) : ℤ) - 2 * ((M + 1 : ℕ) : ℤ) = -1 by push_cast; ring] at this

/-- The even terms of the entry. -/
theorem a_even (N : ℕ) : (a (2 * N) : ℤ) = S N := by
  rw [a_eq_cnt, cnt_eq (2 * N) 0 0 0 (by norm_num) (by norm_num), Tz]
  have hz : ∀ k ∈ Finset.range (2 * (N + 1)), k ∉ Finset.range (2 * N + 1) →
      ((2 * N).choose k : ℤ) * AB k 0 0 * Mz (2 * N - k) 0 = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega)) hz,
    sum_even (fun k => ((2 * N).choose k : ℤ) * AB k 0 0 * Mz (2 * N - k) 0) (fun i => by simp [AB_odd]) (N + 1)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [AB_even, Mz_zero, F, show 2 * N - 2 * t = 2 * (N - t) by omega, bin1_even_zero, bin1_even_neg_one, add_zero]

/-- The odd terms of the entry. -/
theorem a_odd (N : ℕ) : (a (2 * N + 1) : ℤ) = SO N := by
  rw [a_eq_cnt, cnt_eq (2 * N + 1) 0 0 0 (by norm_num) (by norm_num), Tz, show 2 * N + 1 + 1 = 2 * (N + 1) by ring,
    sum_even (fun k => ((2 * N + 1).choose k : ℤ) * AB k 0 0 * Mz (2 * N + 1 - k) 0) (fun i => by simp [AB_odd])
      (N + 1)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.mem_range] at ht
  rw [AB_even, Mz_zero, FO, show 2 * N + 1 - 2 * t = 2 * (N - t) + 1 by omega, bin1_odd_zero, bin1_odd_neg_one,
    zero_add]

/-! ### The cross relation between the odd and the even terms -/

/-- The odd summand against the even one. -/
lemma R1 (n k : ℕ) : FO n k * (2 * ((n : ℤ) + 1)) = F (n + 1) k * ((n : ℤ) + 1 - k) := by
  rcases Nat.lt_or_ge n k with h | h
  · have h0 : FO n k = 0 := by
      rw [FO, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    rw [h0, zero_mul]
    rcases Nat.eq_or_lt_of_le h with e | e
    · subst e
      push_cast
      ring
    · rw [F, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · obtain ⟨M, rfl⟩ : ∃ M, n = k + M := ⟨n - k, by omega⟩
    simp only [FO, F]
    rw [show k + M - k = M by omega, show 2 * (k + M + 1) - 2 * k = 2 * M + 2 by omega,
      show k + M + 1 - k = M + 1 by omega]
    have hA := Nat.choose_mul_succ_eq (2 * (k + M) + 1) (2 * k)
    rw [show 2 * (k + M) + 1 + 1 - 2 * k = 2 * M + 2 by omega,
      show 2 * (k + M) + 1 + 1 = 2 * (k + M + 1) by ring] at hA
    have eA : ((2 * (k + M) + 1).choose (2 * k) : ℤ) * (2 * ((k : ℤ) + M) + 2) =
        ((2 * (k + M + 1)).choose (2 * k) : ℤ) * (2 * M + 2) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) hA
      push_cast at e ⊢
      linear_combination e
    have hG : (2 * M + 2).choose (M + 1) = 2 * (2 * M + 1).choose (M + 1) := by
      rw [show 2 * M + 2 = (2 * M + 1) + 1 by ring, Nat.choose_succ_succ', Nat.choose_symm_half]
      ring
    have eG : ((2 * M + 2).choose (M + 1) : ℤ) = 2 * ((2 * M + 1).choose (M + 1) : ℤ) := by
      exact_mod_cast hG
    push_cast
    linear_combination (w k * ((2 * M + 1).choose (M + 1) : ℤ)) * eA -
      (w k * ((M : ℤ) + 1) * ((2 * (k + M + 1)).choose (2 * k) : ℤ)) * eG

/-- The cross relation, to be shown zero. -/
def X (N : ℕ) : ℤ := 4 * ((N : ℤ) + 1) * SO N - ((N : ℤ) + 2) * S (N + 1) + 6 * (2 * (N : ℤ) + 1) * S N

/-- Its summand. -/
def xk (N k : ℕ) : ℚ := 4 * ((N : ℚ) + 1) * FO N k - ((N : ℚ) + 2) * F (N + 1) k + 6 * (2 * (N : ℚ) + 1) * F N k

/-- The certificate of (N+2)(N+3) X(N+1) - 2(N+1)(2N+3) X(N): Gx(N, k) = cpx(N, k) F(N + 2, k). -/
def cpx (N k : ℕ) : ℚ :=
  (2 * ((N : ℚ) + 2) * k + (4 * (N : ℚ) + 7) * (k : ℚ) ^ 2 + 2 * ((N : ℚ) + 1) * (k : ℚ) ^ 3 - (k : ℚ) ^ 4) /
    ((N : ℚ) + 2)

def Gx (N k : ℕ) : ℚ := cpx N k * F (N + 2) k

lemma certx (N k : ℕ) :
    ((N : ℚ) + 2) * ((N : ℚ) + 3) * xk (N + 1) k - 2 * ((N : ℚ) + 1) * (2 * (N : ℚ) + 3) * xk N k =
      Gx N (k + 1) - Gx N k := by
  simp only [xk]
  push_cast
  rw [show N + 1 + 1 = N + 2 from rfl]
  have r1 := R1 (N + 1) k
  have r0 := R1 N k
  have f1 := Fn (N + 1) k
  have f0 := Fn N k
  have fy := Fk (N + 2) k
  rw [show N + 1 + 1 = N + 2 from rfl] at r1 f1
  push_cast at r1 r0 f1 f0 fy
  have qO1 : (FO (N + 1) k : ℚ) = F (N + 2) k * ((N : ℚ) + 2 - k) / (2 * ((N : ℚ) + 2)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination r1 :
      FO (N + 1) k * (2 * ((N : ℤ) + 2)) = F (N + 2) k * ((N : ℤ) + 2 - k))
  have qF1 : (F (N + 1) k : ℚ) = F (N + 2) k * ((N : ℚ) + 2 - k) ^ 2 / (2 * ((N : ℚ) + 2) * (2 * N + 3)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination -f1 :
      F (N + 1) k * (2 * ((N : ℤ) + 2) * (2 * N + 3)) = F (N + 2) k * ((N : ℤ) + 2 - k) ^ 2)
  have qO0 : (FO N k : ℚ) = F (N + 1) k * ((N : ℚ) + 1 - k) / (2 * ((N : ℚ) + 1)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination r0 :
      FO N k * (2 * ((N : ℤ) + 1)) = F (N + 1) k * ((N : ℤ) + 1 - k))
  have qF0 : (F N k : ℚ) = F (N + 1) k * ((N : ℚ) + 1 - k) ^ 2 / (2 * ((N : ℚ) + 1) * (2 * N + 1)) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination -f0 :
      F N k * (2 * ((N : ℤ) + 1) * (2 * N + 1)) = F (N + 1) k * ((N : ℤ) + 1 - k) ^ 2)
  have qy : (F (N + 2) (k + 1) : ℚ) =
      4 * (2 * k + 3) * ((N : ℚ) + 2 - k) ^ 2 * F (N + 2) k / ((2 * (k : ℚ) + 2) * ((k : ℚ) + 2) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination fy :
      F (N + 2) (k + 1) * ((2 * (k : ℤ) + 2) * ((k : ℤ) + 2) ^ 2) =
        4 * (2 * k + 3) * ((N : ℤ) + 2 - k) ^ 2 * F (N + 2) k)
  simp only [Gx, cpx]
  rw [qO0, qF0, qF1, qO1, qy]
  push_cast
  field_simp
  ring

lemma S_ext (n L : ℕ) (hL : n + 1 ≤ L) : (S n : ℚ) = ∑ k ∈ Finset.range L, (F n k : ℚ) := by
  rw [S, Int.cast_sum]
  refine Finset.sum_subset (Finset.range_subset_range.2 hL) (fun k _ hk => ?_)
  rw [Finset.mem_range, not_lt] at hk
  rw [F, Nat.choose_eq_zero_of_lt (by omega)]
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
  rw [SO_ext N L (by omega), S_ext (N + 1) L hL, S_ext N L (by omega), Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rfl

theorem rec_X (N : ℕ) : ((N : ℤ) + 2) * ((N : ℤ) + 3) * X (N + 1) - 2 * ((N : ℤ) + 1) * (2 * N + 3) * X N = 0 := by
  have g0 : Gx N 0 = 0 := by simp [Gx, cpx]
  have g1 : Gx N (N + 3) = 0 := by
    rw [Gx, F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hq : ((N : ℚ) + 2) * ((N : ℚ) + 3) * X (N + 1) - 2 * ((N : ℚ) + 1) * (2 * N + 3) * X N = 0 := by
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
    have hne : ((N : ℤ) + 2) * ((N : ℤ) + 3) ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left hne

/-! ### The recurrence -/

/-- Mathar's expression at n = 2N + 6, from the cross relations and the abb recurrence. -/
lemma mathar_even (N : ℕ) :
    ((2 * (N : ℤ) + 6) + 2) * ((2 * (N : ℤ) + 6) + 3) ^ 2 * S (N + 3) +
      4 * (2 * (2 * (N : ℤ) + 6) ^ 3 + 7 * (2 * (N : ℤ) + 6) ^ 2 + 7 * (2 * (N : ℤ) + 6) + 4) * SO (N + 2) +
      4 * (-25 * (2 * (N : ℤ) + 6) ^ 3 - 28 * (2 * (N : ℤ) + 6) ^ 2 + 54 * (2 * (N : ℤ) + 6) + 35) * S (N + 2) +
      32 * (-10 * (2 * (N : ℤ) + 6) ^ 3 + 26 * (2 * (N : ℤ) + 6) ^ 2 - 23 * (2 * (N : ℤ) + 6) + 40) * SO (N + 1) +
      48 * ((2 * (N : ℤ) + 6) - 3) * (53 * (2 * (N : ℤ) + 6) ^ 2 - 161 * (2 * (N : ℤ) + 6) + 77) * S (N + 1) +
      576 * (2 * (2 * (N : ℤ) + 6) + 3) * ((2 * (N : ℤ) + 6) - 3) * ((2 * (N : ℤ) + 6) - 4) * SO N +
      (-8640) * ((2 * (N : ℤ) + 6) - 5) * ((2 * (N : ℤ) + 6) - 3) * ((2 * (N : ℤ) + 6) - 4) * S N = 0 := by
  have hX0 := X_eq_zero N
  have hX1 := X_eq_zero (N + 1)
  have hX2 := X_eq_zero (N + 2)
  have hb0 := b_eq_zero N
  have hb1 := b_eq_zero (N + 1)
  simp only [X, b, l0, l1, l2, Nat.add_assoc, Nat.reduceAdd] at hX0 hX1 hX2 hb0 hb1
  push_cast at hX0 hX1 hX2 hb0 hb1
  have hD : (4 * ((N : ℤ) + 1) * 4 * ((N : ℤ) + 2) * 4 * ((N : ℤ) + 3) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.1 ?_).resolve_left hD
  linear_combination (4976640 + 13768704 * (N : ℤ) + 14376960 * (N : ℤ) ^ 2 + 7096320 * (N : ℤ) ^ 3 + 1658880 * (N : ℤ) ^ 4 + 147456 * (N : ℤ) ^ 5) * hX0 +
    (-2030592 - 5137408 * (N : ℤ) - 4862976 * (N : ℤ) ^ 2 - 2194432 * (N : ℤ) ^ 3 - 479232 * (N : ℤ) ^ 4 - 40960 * (N : ℤ) ^ 5) * hX1 +
    (93440 + 218752 * (N : ℤ) + 186624 * (N : ℤ) ^ 2 + 74368 * (N : ℤ) ^ 3 + 14080 * (N : ℤ) ^ 4 + 1024 * (N : ℤ) ^ 5) * hX2 +
    (-230400 - 436224 * (N : ℤ) - 248832 * (N : ℤ) ^ 2 - 43008 * (N : ℤ) ^ 3) * hb0 +
    (9728 + 17664 * (N : ℤ) + 9472 * (N : ℤ) ^ 2 + 1536 * (N : ℤ) ^ 3) * hb1

/-- Mathar's expression at n = 2N + 7, from the cross relations and the abb recurrence. -/
lemma mathar_odd (N : ℕ) :
    ((2 * (N : ℤ) + 7) + 2) * ((2 * (N : ℤ) + 7) + 3) ^ 2 * SO (N + 3) +
      4 * (2 * (2 * (N : ℤ) + 7) ^ 3 + 7 * (2 * (N : ℤ) + 7) ^ 2 + 7 * (2 * (N : ℤ) + 7) + 4) * S (N + 3) +
      4 * (-25 * (2 * (N : ℤ) + 7) ^ 3 - 28 * (2 * (N : ℤ) + 7) ^ 2 + 54 * (2 * (N : ℤ) + 7) + 35) * SO (N + 2) +
      32 * (-10 * (2 * (N : ℤ) + 7) ^ 3 + 26 * (2 * (N : ℤ) + 7) ^ 2 - 23 * (2 * (N : ℤ) + 7) + 40) * S (N + 2) +
      48 * ((2 * (N : ℤ) + 7) - 3) * (53 * (2 * (N : ℤ) + 7) ^ 2 - 161 * (2 * (N : ℤ) + 7) + 77) * SO (N + 1) +
      576 * (2 * (2 * (N : ℤ) + 7) + 3) * ((2 * (N : ℤ) + 7) - 3) * ((2 * (N : ℤ) + 7) - 4) * S (N + 1) +
      (-8640) * ((2 * (N : ℤ) + 7) - 5) * ((2 * (N : ℤ) + 7) - 3) * ((2 * (N : ℤ) + 7) - 4) * SO N = 0 := by
  have hX0 := X_eq_zero N
  have hX1 := X_eq_zero (N + 1)
  have hX2 := X_eq_zero (N + 2)
  have hX3 := X_eq_zero (N + 3)
  have hb0 := b_eq_zero N
  have hb1 := b_eq_zero (N + 1)
  have hb2 := b_eq_zero (N + 2)
  simp only [X, b, l0, l1, l2, Nat.add_assoc, Nat.reduceAdd] at hX0 hX1 hX2 hX3 hb0 hb1 hb2
  push_cast at hX0 hX1 hX2 hX3 hb0 hb1 hb2
  have hD : (4 * ((N : ℤ) + 1) * 4 * ((N : ℤ) + 2) * 4 * ((N : ℤ) + 3) * 4 * ((N : ℤ) + 4) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.1 ?_).resolve_left hD
  linear_combination (-318504960 - 1035141120 * (N : ℤ) - 1344798720 * (N : ℤ) ^ 2 - 895795200 * (N : ℤ) ^ 3 - 322928640 * (N : ℤ) ^ 4 - 59719680 * (N : ℤ) ^ 5 - 4423680 * (N : ℤ) ^ 6) * hX0 +
    (228114432 + 646582272 * (N : ℤ) + 720893952 * (N : ℤ) ^ 2 + 410050560 * (N : ℤ) ^ 3 + 126486528 * (N : ℤ) ^ 4 + 20164608 * (N : ℤ) ^ 5 + 1302528 * (N : ℤ) ^ 6) * hX1 +
    (-19525632 - 50607104 * (N : ℤ) - 50380288 * (N : ℤ) ^ 2 - 25160704 * (N : ℤ) ^ 3 - 6735360 * (N : ℤ) ^ 4 - 924672 * (N : ℤ) ^ 5 - 51200 * (N : ℤ) ^ 6) * hX2 +
    (345600 + 848640 * (N : ℤ) + 784384 * (N : ℤ) ^ 2 + 357376 * (N : ℤ) ^ 3 + 86016 * (N : ℤ) ^ 4 + 10496 * (N : ℤ) ^ 5 + 512 * (N : ℤ) ^ 6) * hX3 +
    (8847360 + 18432000 * (N : ℤ) + 12902400 * (N : ℤ) ^ 2 + 3686400 * (N : ℤ) ^ 3 + 368640 * (N : ℤ) ^ 4) * hb0 +
    (-417792 - 894976 * (N : ℤ) - 652288 * (N : ℤ) ^ 2 - 195584 * (N : ℤ) ^ 3 - 20480 * (N : ℤ) ^ 4) * hb1 +
    (13824 + 28416 * (N : ℤ) + 19456 * (N : ℤ) ^ 2 + 5376 * (N : ℤ) ^ 3 + 512 * (N : ℤ) ^ 4) * hb2

/-- Mathar's recurrence, for every n ≥ 6. -/
theorem conjecture :
    ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 2) * ((n : ℤ) + 3) ^ 2 * (a n : ℤ) +
      4 * (2 * (n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 2 + 7 * (n : ℤ) + 4) * (a (n - 1) : ℤ) +
      4 * (-25 * (n : ℤ) ^ 3 - 28 * (n : ℤ) ^ 2 + 54 * (n : ℤ) + 35) * (a (n - 2) : ℤ) +
      32 * (-10 * (n : ℤ) ^ 3 + 26 * (n : ℤ) ^ 2 - 23 * (n : ℤ) + 40) * (a (n - 3) : ℤ) +
      48 * ((n : ℤ) - 3) * (53 * (n : ℤ) ^ 2 - 161 * (n : ℤ) + 77) * (a (n - 4) : ℤ) +
      576 * (2 * (n : ℤ) + 3) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 5) : ℤ) -
      8640 * ((n : ℤ) - 5) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 6) : ℤ) = 0 := by
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
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 5 ∧ a 3 = 12 ∧ a 4 = 62 ∧ a 5 = 200 ∧ a 6 = 1065 ∧ a 7 = 3990 ∧ a 8 =
    21714 ∧ a 9 = 89082 ∧ a 10 = 492366 ∧ a 11 = 2147376 ∧ a 12 = 12004740 ∧ a 13 = 54718092 ∧ a 14
    = 308559537 ∧ a 15 = 1454116950 ∧ a 16 = 8255788970 ∧ a 17 = 39935276810 ∧ a 18 = 227976044010 ∧
    a 19 = 1126178350440 ∧ a 20 = 6457854821340 ∧ a 21 = 32456552441040 ∧ a 22 = 186814834574550 ∧ a
    23 = 952569927106980 ∧ a 24 = 5500292590186380 ∧ a 25 = 28391993275117500 := by
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

end OMA.S_oeis_a302182

theorem OMA.solution : type_of% @OMA.S_oeis_a302182.main :=
  OMA.S_oeis_a302182.conjecture
