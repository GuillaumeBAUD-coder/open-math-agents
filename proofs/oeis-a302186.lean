import OMAStatements.S_oeis_a302186

namespace OMA.S_oeis_a302186




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

/-- The walks of N steps from the point (h, y, ·) that keep x ≥ 0 and y ≥ 0 and end with x = 0. -/
def cnt (N : ℕ) (h y : ℤ) : ℕ :=
  (Finset.univ.filter (fun w : Fin N → Fin 6 =>
    (∀ t ≤ N, 0 ≤ h + (pt w t).1 ∧ 0 ≤ y + (pt w t).2.1) ∧ h + (pt w N).1 = 0)).card

lemma a_eq_cnt (n : ℕ) : a n = cnt n 0 0 := by
  simp only [a, cnt, zero_add]

lemma cnt_neg (N : ℕ) {h y : ℤ} (hh : h < 0 ∨ y < 0) : cnt N h y = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hw
  have h0 := hw.1 0 (Nat.zero_le _)
  rw [pt_zero] at h0
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero] at h0
  omega

lemma cond_cons {N : ℕ} (c : Fin 6) (w : Fin N → Fin 6) (h y : ℤ) (hh : 0 ≤ h) (hy : 0 ≤ y) :
    ((∀ t ≤ N + 1, 0 ≤ h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).1 ∧
        0 ≤ y + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).2.1) ∧
      h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).1 = 0) ↔
    ((∀ t ≤ N, 0 ≤ (h + (step c).1) + (pt w t).1 ∧ 0 ≤ (y + (step c).2.1) + (pt w t).2.1) ∧
      (h + (step c).1) + (pt w N).1 = 0) := by
  rw [pt_cons]
  simp only [Prod.fst_add, ← add_assoc]
  refine and_congr ⟨fun H t ht => ?_, fun H t ht => ?_⟩ Iff.rfl
  · have := H (t + 1) (by omega)
    simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc] at this
    exact this
  · rcases t with _ | t
    · simp only [pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
      exact ⟨hh, hy⟩
    · simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc]
      exact H t (by omega)

lemma cnt_succ_sum (N : ℕ) (h y : ℤ) (hh : 0 ≤ h) (hy : 0 ≤ y) :
    cnt (N + 1) h y = ∑ c : Fin 6, cnt N (h + (step c).1) (y + (step c).2.1) := by
  rw [cnt, Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin 6)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [cnt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact if_congr (cond_cons c w h y hh hy) rfl rfl

lemma cnt_succ (N : ℕ) (h y : ℤ) (hh : 0 ≤ h) (hy : 0 ≤ y) :
    (cnt (N + 1) h y : ℤ) = cnt N (h + 1) y + cnt N (h - 1) y + cnt N h (y + 1) + cnt N h (y - 1) +
      2 * cnt N h y := by
  rw [cnt_succ_sum N h y hh hy, Fin.sum_univ_six]
  simp [step]
  ring_nf

/-! ### The x-steps: a ±1 walk back to 0 that stays ≥ 0 -/

/-- The ±1 walks of k steps from h back to 0 that stay ≥ 0, by reflection in -1. -/
def D (k : ℕ) (h : ℤ) : ℤ := bin1 k h - bin1 k (h + 2)

lemma D_succ (k : ℕ) (h : ℤ) : D (k + 1) h = D k (h + 1) + D k (h - 1) := by
  simp only [D, bin1]
  rw [show h + 2 + 1 = h + 1 + 2 by ring, show h + 2 - 1 = h + 1 by ring, show h - 1 + 2 = h + 1 by ring]
  ring

lemma D_neg_one (k : ℕ) : D k (-1) = 0 := by
  rw [D, show (-1 : ℤ) + 2 = 1 by norm_num, bin1_neg, sub_self]

/-- The Catalan numbers, as C(2i, i) - C(2i, i+1). -/
def cat (i : ℕ) : ℤ := ((2 * i).choose i : ℤ) - ((2 * i).choose (i + 1) : ℤ)

lemma D_even (i : ℕ) : D (2 * i) 0 = cat i := by
  have h0 : bin1 (2 * i) 0 = (2 * i).choose i := by
    have := bin1_choose (2 * i) i
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * (i : ℤ) = 0 by push_cast; ring] at this
  have h2 : bin1 (2 * i) 2 = (2 * i).choose (i + 1) := by
    have := bin1_choose (2 * i) (i + 1)
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * ((i + 1 : ℕ) : ℤ) = -2 by push_cast; ring, bin1_neg] at this
  rw [D, zero_add, h0, h2, cat]

lemma D_odd (i : ℕ) : D (2 * i + 1) 0 = 0 := by
  have h0 : bin1 (2 * i + 1) 0 = 0 := by
    have := bin1_odd (2 * i + 1) i
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * (i : ℤ) - 1 = 0 by push_cast; ring] at this
  have h2 : bin1 (2 * i + 1) 2 = 0 := by
    have := bin1_odd (2 * i + 1) (i - 1)
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * ((i : ℤ) - 1) - 1 = 2 by push_cast; ring] at this
  rw [D, zero_add, h0, h2, sub_zero]

/-! ### The y- and z-steps: a walk that keeps y ≥ 0, by reflection and a cumulative count -/

/-- The walks of m steps among ±y, ±z whose y-coordinate ends at least -t (by recursion on m). -/
def Cum : ℕ → ℤ → ℤ
  | 0, t => if 0 ≤ t then 1 else 0
  | m + 1, t => Cum m (t + 1) + Cum m (t - 1) + 2 * Cum m t

/-- The walks of exactly one final y-displacement: pairing each of the four steps with two ±1 steps. -/
lemma Cum_diff : ∀ (m : ℕ) (t : ℤ), Cum m t - Cum m (t - 1) = bin1 (2 * m) (2 * t)
  | 0, t => by
    simp only [Cum, bin1]
    split_ifs <;> omega
  | m + 1, t => by
    have h1 := Cum_diff m (t + 1)
    have h2 := Cum_diff m t
    have h3 := Cum_diff m (t - 1)
    rw [show t + 1 - 1 = t by ring] at h1
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, bin1, bin1, bin1,
      show 2 * t + 1 + 1 = 2 * (t + 1) by ring, show 2 * t + 1 - 1 = 2 * t by ring,
      show 2 * t - 1 + 1 = 2 * t by ring, show 2 * t - 1 - 1 = 2 * (t - 1) by ring]
    simp only [Cum]
    rw [show t - 1 + 1 = t by ring]
    linear_combination h1 + 2 * h2 + h3

/-- The walks of m steps among ±y, ±z from y that keep y ≥ 0, by reflection in -1. -/
def E (m : ℕ) (y : ℤ) : ℤ := Cum m y - Cum m (-2 - y)

lemma E_succ (m : ℕ) (y : ℤ) : E (m + 1) y = E m (y + 1) + E m (y - 1) + 2 * E m y := by
  simp only [E, Cum]
  rw [show -2 - y + 1 = -1 - y by ring, show -2 - y - 1 = -3 - y by ring, show -2 - (y + 1) = -3 - y by ring,
    show -2 - (y - 1) = -1 - y by ring]
  ring

lemma E_neg_one (m : ℕ) : E m (-1) = 0 := by
  rw [E, show (-2 : ℤ) - -1 = -1 by norm_num, sub_self]

lemma E_zero (m : ℕ) : E m 0 = ((2 * m + 1).choose (m + 1) : ℤ) := by
  have h0 := Cum_diff m 0
  have h1 := Cum_diff m (-1)
  rw [show (0 : ℤ) - 1 = -1 by norm_num, mul_zero] at h0
  rw [show (-1 : ℤ) - 1 = -2 by norm_num, show (2 : ℤ) * -1 = -2 by norm_num] at h1
  have b0 : bin1 (2 * m) 0 = (2 * m).choose m := by
    have := bin1_choose (2 * m) m
    rwa [show ((2 * m : ℕ) : ℤ) - 2 * (m : ℤ) = 0 by push_cast; ring] at this
  have b2 : bin1 (2 * m) (-2) = (2 * m).choose (m + 1) := by
    have := bin1_choose (2 * m) (m + 1)
    rwa [show ((2 * m : ℕ) : ℤ) - 2 * ((m + 1 : ℕ) : ℤ) = -2 by push_cast; ring] at this
  rw [E, show (-2 : ℤ) - 0 = -2 by norm_num, Nat.choose_succ_succ', Nat.cast_add]
  linear_combination h0 + h1 + b0 + b2

/-! ### The x-steps and the (y, z)-steps interleaved -/

/-- Conv N f g = Sum_k C(N, k) f(k) g(N - k). -/
def Conv (N : ℕ) (f g : ℕ → ℤ) : ℤ := ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * g (N - k)

lemma Conv_succ (N : ℕ) (f g : ℕ → ℤ) :
    Conv (N + 1) f g = Conv N (fun k => f (k + 1)) g + Conv N f (fun j => g (j + 1)) := by
  have h1 : Conv (N + 1) f g = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * g (N - k) +
      ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * g (N - k) + f 0 * g (N + 1) := by
    rw [Conv, Finset.sum_range_succ', ← Finset.sum_add_distrib]
    simp only [Nat.choose_succ_succ', Nat.add_sub_add_right, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_add,
      Nat.cast_one, one_mul, add_mul]
  have h2 : Conv N f (fun j => g (j + 1)) =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * g (N - k) + f 0 * g (N + 1) := by
    rw [Conv, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    rw [show N - (k + 1) + 1 = N - k by omega]
  have h3 : ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * g (N - k) =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * g (N - k) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero]
  have h4 : Conv N (fun k => f (k + 1)) g =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * g (N - k) := rfl
  rw [h1, h3]
  linarith [h2, h4]

lemma cnt_zero (h y : ℤ) (hh : -1 ≤ h) (hy : -1 ≤ y) : (cnt 0 h y : ℤ) = D 0 h * E 0 y := by
  have hc : cnt 0 h y = if h = 0 ∧ 0 ≤ y then 1 else 0 := by
    rw [cnt, Finset.card_filter, Fintype.sum_unique]
    simp only [nonpos_iff_eq_zero, forall_eq, pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
    by_cases h0 : h = 0 <;> by_cases y0 : 0 ≤ y <;> simp [h0, y0]
  rw [hc]
  simp only [D, E, bin1, Cum]
  split_ifs <;> omega

/-- The count from any start with x, y ≥ -1. -/
theorem cnt_eq (N : ℕ) : ∀ h y : ℤ, -1 ≤ h → -1 ≤ y → (cnt N h y : ℤ) = Conv N (fun k => D k h) (fun j => E j y) := by
  induction N with
  | zero =>
    intro h y hh hy
    rw [cnt_zero h y hh hy]
    simp [Conv]
  | succ N ih =>
    intro h y hh hy
    rcases eq_or_lt_of_le hh with e | hh'
    · rw [← e, cnt_neg _ (Or.inl (by norm_num)), Nat.cast_zero]
      simp [Conv, D_neg_one]
    rcases eq_or_lt_of_le hy with e | hy'
    · rw [← e, cnt_neg _ (Or.inr (by norm_num)), Nat.cast_zero]
      simp [Conv, E_neg_one]
    have h0 : 0 ≤ h := by omega
    have y0 : 0 ≤ y := by omega
    have hs1 : Conv N (fun k => D (k + 1) h) (fun j => E j y) =
        Conv N (fun k => D k (h + 1)) (fun j => E j y) + Conv N (fun k => D k (h - 1)) (fun j => E j y) := by
      simp only [Conv, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [D_succ]; ring)
    have hs2 : Conv N (fun k => D k h) (fun j => E (j + 1) y) =
        Conv N (fun k => D k h) (fun j => E j (y + 1)) + Conv N (fun k => D k h) (fun j => E j (y - 1)) +
          2 * Conv N (fun k => D k h) (fun j => E j y) := by
      simp only [Conv, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [E_succ]; ring)
    rw [cnt_succ N h y h0 y0, ih (h + 1) y (by omega) hy, ih (h - 1) y (by omega) hy, ih h (y + 1) hh (by omega),
      ih h (y - 1) hh (by omega), ih h y hh hy, Conv_succ, hs1, hs2]
    ring

/-! ### The sum -/

/-- The summand: 2i x-steps (a Catalan walk) and n - 2i steps among ±y, ±z keeping y ≥ 0 (C(2M+1, M+1) of
them, M = n - 2i), interleaved. -/
def F (n i : ℕ) : ℤ := (n.choose (2 * i) : ℤ) * cat i * ((2 * (n - 2 * i) + 1).choose (n - 2 * i + 1) : ℤ)

/-- The sum over i. -/
def S (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n + 1), F n i

/-- The count of the entry is the sum. -/
theorem a_eq_S (n : ℕ) : (a n : ℤ) = S n := by
  rw [a_eq_cnt, cnt_eq n 0 0 (by norm_num) (by norm_num), Conv]
  have hz : ∀ k ∈ Finset.range (2 * (n + 1)), k ∉ Finset.range (n + 1) →
      (n.choose k : ℤ) * D k 0 * E (n - k) 0 = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega)) hz,
    sum_even (fun k => (n.choose k : ℤ) * D k 0 * E (n - k) 0) (fun i => by simp [D_odd]) (n + 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [D_even, E_zero, F]

/-! ### Shift relations -/

lemma cat_mul (i : ℕ) : cat i * ((i : ℤ) + 1) = ((2 * i).choose i : ℤ) := by
  have hc := Nat.choose_succ_right_eq (2 * i) i
  rw [show 2 * i - i = i by omega] at hc
  have hc' : ((2 * i).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((2 * i).choose i : ℤ) * i := by
    exact_mod_cast hc
  simp only [cat]
  linear_combination -hc'

lemma cat_succ (i : ℕ) : cat (i + 1) * ((i : ℤ) + 2) = 2 * (2 * i + 1) * cat i := by
  have h1 := cat_mul (i + 1)
  have h0 := cat_mul i
  have hb := Nat.succ_mul_centralBinom_succ i
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hb
  have hb' : ((i : ℤ) + 1) * ((2 * (i + 1)).choose (i + 1) : ℤ) = 2 * (2 * i + 1) * ((2 * i).choose i : ℤ) := by
    exact_mod_cast hb
  push_cast at h1
  have key : (cat (i + 1) * ((i : ℤ) + 2) - 2 * (2 * i + 1) * cat i) * ((i : ℤ) + 1) = 0 := by
    linear_combination ((i : ℤ) + 1) * h1 - 2 * (2 * (i : ℤ) + 1) * h0 + hb'
  have hne : ((i : ℤ) + 1) ≠ 0 := by positivity
  linear_combination (mul_eq_zero.1 key).resolve_right hne

lemma gg_succ (M : ℕ) : ((2 * (M + 1) + 1).choose (M + 1 + 1) : ℤ) * ((M : ℤ) + 2) =
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

/-- One more step in n. -/
lemma Fn (n i : ℕ) : F (n + 1) i * (((n : ℤ) + 1 - 2 * i) * ((n : ℤ) + 2 - 2 * i)) =
    2 * ((n : ℤ) + 1) * (2 * n - 4 * i + 3) * F n i := by
  rcases Nat.lt_or_ge n (2 * i) with h | h
  · have h0 : F n i = 0 := by
      rw [F, Nat.choose_eq_zero_of_lt h]
      simp
    rw [h0, mul_zero]
    rcases Nat.lt_or_ge (n + 1) (2 * i) with h' | h'
    · rw [F, Nat.choose_eq_zero_of_lt h']
      simp
    · have e : (n : ℤ) + 1 - 2 * i = 0 := by omega
      rw [e]
      ring
  · obtain ⟨M, rfl⟩ : ∃ M, n = 2 * i + M := ⟨n - 2 * i, by omega⟩
    simp only [F]
    rw [show 2 * i + M + 1 - 2 * i = M + 1 by omega, show 2 * i + M - 2 * i = M by omega]
    have hA := Nat.choose_mul_succ_eq (2 * i + M) (2 * i)
    rw [show 2 * i + M + 1 - 2 * i = M + 1 by omega] at hA
    have eA : ((2 * i + M).choose (2 * i) : ℤ) * ((2 * (i : ℤ) + M) + 1) =
        ((2 * i + M + 1).choose (2 * i) : ℤ) * ((M : ℤ) + 1) := by
      exact_mod_cast hA
    have eG := gg_succ M
    push_cast
    linear_combination (cat i * ((M : ℤ) + 1) * ((2 * i + M + 1).choose (2 * i) : ℤ)) * eG -
      (2 * (2 * (M : ℤ) + 3) * cat i * ((2 * M + 1).choose (M + 1) : ℤ)) * eA

/-- One more step in i. -/
lemma Fk (n i : ℕ) : F n (i + 1) * (2 * (2 * (i : ℤ) + 2) * ((i : ℤ) + 2) *
      ((2 * ((n : ℤ) - 2 * i) + 1) * (2 * ((n : ℤ) - 2 * i) - 1))) =
    ((n : ℤ) - 2 * i) ^ 2 * (((n : ℤ) - 2 * i) ^ 2 - 1) * F n i := by
  rcases Nat.lt_or_ge n (2 * i + 2) with h | h
  · rw [F, Nat.choose_eq_zero_of_lt (show n < 2 * (i + 1) by omega), Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    rcases Nat.lt_or_ge n (2 * i) with h' | h'
    · rw [F, Nat.choose_eq_zero_of_lt h']
      simp
    · rcases Nat.eq_or_lt_of_le h' with e | e
      · have : (n : ℤ) - 2 * i = 0 := by omega
        rw [this]
        ring
      · have : (n : ℤ) - 2 * i = 1 := by omega
        rw [this]
        ring
  · obtain ⟨M, rfl⟩ : ∃ M, n = 2 * i + 2 + M := ⟨n - 2 * i - 2, by omega⟩
    simp only [F]
    rw [show 2 * i + 2 + M - 2 * (i + 1) = M by omega, show 2 * i + 2 + M - 2 * i = M + 1 + 1 by omega,
      show 2 * (i + 1) = 2 * i + 2 by ring]
    have e1 := Nat.choose_succ_right_eq (2 * i + 2 + M) (2 * i)
    have e2 := Nat.choose_succ_right_eq (2 * i + 2 + M) (2 * i + 1)
    rw [show 2 * i + 2 + M - 2 * i = M + 2 by omega] at e1
    rw [show 2 * i + 2 + M - (2 * i + 1) = M + 1 by omega, show 2 * i + 1 + 1 = 2 * i + 2 by ring] at e2
    have e1' : ((2 * i + 2 + M).choose (2 * i + 1) : ℤ) * (2 * i + 1) =
        ((2 * i + 2 + M).choose (2 * i) : ℤ) * ((M : ℤ) + 2) := by
      exact_mod_cast e1
    have e2' : ((2 * i + 2 + M).choose (2 * i + 2) : ℤ) * (2 * i + 2) =
        ((2 * i + 2 + M).choose (2 * i + 1) : ℤ) * ((M : ℤ) + 1) := by
      exact_mod_cast e2
    have ec := cat_succ i
    have g1 := gg_succ M
    have g2 := gg_succ (M + 1)
    push_cast at g2 ⊢
    linear_combination (2 * ((2 * M + 1).choose (M + 1) : ℤ) * ((2 * (M : ℤ) + 5) * (2 * M + 3)) *
        (cat (i + 1) * ((i : ℤ) + 2))) * e2' +
      (2 * ((2 * i + 2 + M).choose (2 * i + 1) : ℤ) * ((M : ℤ) + 1) * ((2 * M + 1).choose (M + 1) : ℤ) *
        ((2 * (M : ℤ) + 5) * (2 * M + 3))) * ec +
      (4 * ((M : ℤ) + 1) * cat i * ((2 * M + 1).choose (M + 1) : ℤ) * ((2 * (M : ℤ) + 5) * (2 * M + 3))) * e1' -
      (((M : ℤ) + 2) * ((M : ℤ) + 1) * ((2 * i + 2 + M).choose (2 * i) : ℤ) * cat i * (2 * (2 * (M : ℤ) + 5))) * g1 -
      (((M : ℤ) + 2) * ((M : ℤ) + 1) * ((2 * i + 2 + M).choose (2 * i) : ℤ) * cat i * ((M : ℤ) + 2)) * g2

/-! ### The minimal operator M, an order-4 telescoper, and its certificate -/

/-- The order-3 operator of the sum at n = m: M(m) = p0 S(m) + p1 S(m+1) + p2 S(m+2) + p3 S(m+3). -/
def p0 (m : ℕ) : ℤ := 1008 + 1704 * (m : ℤ) + 792 * (m : ℤ) ^ 2 + 96 * (m : ℤ) ^ 3
def p1 (m : ℕ) : ℤ := -72 - 204 * (m : ℤ) - 116 * (m : ℤ) ^ 2 - 16 * (m : ℤ) ^ 3
def p2 (m : ℕ) : ℤ := -2112 - 1450 * (m : ℤ) - 326 * (m : ℤ) ^ 2 - 24 * (m : ℤ) ^ 3
def p3 (m : ℕ) : ℤ := 510 + 307 * (m : ℤ) + 61 * (m : ℤ) ^ 2 + 4 * (m : ℤ) ^ 3

/-- The telescoper (4m+15)(m+5) M(m+1) - 2(m+3)(4m+19) M(m). -/
def t0 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 3) * (4 * m + 19) * p0 m
def t1 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 3) * (4 * m + 19) * p1 m + (4 * (m : ℤ) + 15) * (m + 5) * p0 (m + 1)
def t2 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 3) * (4 * m + 19) * p2 m + (4 * (m : ℤ) + 15) * (m + 5) * p1 (m + 1)
def t3 (m : ℕ) : ℤ := -2 * ((m : ℤ) + 3) * (4 * m + 19) * p3 m + (4 * (m : ℤ) + 15) * (m + 5) * p2 (m + 1)
def t4 (m : ℕ) : ℤ := (4 * (m : ℤ) + 15) * (m + 5) * p3 (m + 1)

/-- The certificate: G(m, k) = cp(m, k) / ((2m - 4k + 9)(2m - 4k + 7)) F(m + 4, k), cp a polynomial in k. -/
def cp (m k : ℕ) : ℚ :=
  ((-2163420 - 2822712 * (m : ℚ) - 1517988 * (m : ℚ) ^ 2 - 430496 * (m : ℚ) ^ 3 - 67860 * (m : ℚ) ^ 4 -
        5632 * (m : ℚ) ^ 5 - 192 * (m : ℚ) ^ 6) * (k : ℚ) +
      (-300300 - 921224 * (m : ℚ) - 757028 * (m : ℚ) ^ 2 - 281856 * (m : ℚ) ^ 3 - 53780 * (m : ℚ) ^ 4 -
        5120 * (m : ℚ) ^ 5 - 192 * (m : ℚ) ^ 6) * (k : ℚ) ^ 2 +
      (1746864 + 1868592 * (m : ℚ) + 774368 * (m : ℚ) ^ 2 + 154272 * (m : ℚ) ^ 3 + 14592 * (m : ℚ) ^ 4 +
        512 * (m : ℚ) ^ 5) * (k : ℚ) ^ 3 +
      (-299040 - 156416 * (m : ℚ) - 14240 * (m : ℚ) ^ 2 + 3584 * (m : ℚ) ^ 3 + 512 * (m : ℚ) ^ 4) * (k : ℚ) ^ 4 +
      (-157248 - 113280 * (m : ℚ) - 26624 * (m : ℚ) ^ 2 - 2048 * (m : ℚ) ^ 3) * (k : ℚ) ^ 5 +
      (25536 + 10240 * (m : ℚ) + 1024 * (m : ℚ) ^ 2) * (k : ℚ) ^ 6) / ((m : ℚ) + 4)

def G (m k : ℕ) : ℚ := cp m k / ((2 * (m : ℚ) - 4 * k + 9) * (2 * (m : ℚ) - 4 * k + 7)) * F (m + 4) k

/-- The certificate identity, term by term, for every k. -/
lemma cert (m k : ℕ) :
    (t0 m : ℚ) * F m k + t1 m * F (m + 1) k + t2 m * F (m + 2) k + t3 m * F (m + 3) k + t4 m * F (m + 4) k =
      G m (k + 1) - G m k := by
  have e3 := Fn (m + 3) k
  have e2 := Fn (m + 2) k
  have e1 := Fn (m + 1) k
  have e0 := Fn m k
  have ey := Fk (m + 4) k
  rw [show m + 3 + 1 = m + 4 from rfl] at e3
  rw [show m + 2 + 1 = m + 3 from rfl] at e2
  rw [show m + 1 + 1 = m + 2 from rfl] at e1
  push_cast at e3 e2 e1 e0 ey
  have n9 : (2 * (m : ℚ) - 4 * k + 9) ≠ 0 := by
    have : (2 * (m : ℤ) - 4 * k + 9) ≠ 0 := by omega
    exact_mod_cast this
  have n7 : (2 * (m : ℚ) - 4 * k + 7) ≠ 0 := by
    have : (2 * (m : ℤ) - 4 * k + 7) ≠ 0 := by omega
    exact_mod_cast this
  have n5 : (2 * (m : ℚ) - 4 * k + 5) ≠ 0 := by
    have : (2 * (m : ℤ) - 4 * k + 5) ≠ 0 := by omega
    exact_mod_cast this
  have n3 : (2 * (m : ℚ) - 4 * k + 3) ≠ 0 := by
    have : (2 * (m : ℤ) - 4 * k + 3) ≠ 0 := by omega
    exact_mod_cast this
  have q3 : (F (m + 3) k : ℚ) = F (m + 4) k * (((m : ℚ) + 4 - 2 * k) * ((m : ℚ) + 5 - 2 * k)) /
      (2 * ((m : ℚ) + 4) * (2 * m - 4 * k + 9)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n9)]
    exact_mod_cast (by linear_combination -e3 :
      F (m + 3) k * (2 * ((m : ℤ) + 4) * (2 * m - 4 * k + 9)) =
        F (m + 4) k * (((m : ℤ) + 4 - 2 * k) * ((m : ℤ) + 5 - 2 * k)))
  have q2 : (F (m + 2) k : ℚ) = F (m + 3) k * (((m : ℚ) + 3 - 2 * k) * ((m : ℚ) + 4 - 2 * k)) /
      (2 * ((m : ℚ) + 3) * (2 * m - 4 * k + 7)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n7)]
    exact_mod_cast (by linear_combination -e2 :
      F (m + 2) k * (2 * ((m : ℤ) + 3) * (2 * m - 4 * k + 7)) =
        F (m + 3) k * (((m : ℤ) + 3 - 2 * k) * ((m : ℤ) + 4 - 2 * k)))
  have q1 : (F (m + 1) k : ℚ) = F (m + 2) k * (((m : ℚ) + 2 - 2 * k) * ((m : ℚ) + 3 - 2 * k)) /
      (2 * ((m : ℚ) + 2) * (2 * m - 4 * k + 5)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n5)]
    exact_mod_cast (by linear_combination -e1 :
      F (m + 1) k * (2 * ((m : ℤ) + 2) * (2 * m - 4 * k + 5)) =
        F (m + 2) k * (((m : ℤ) + 2 - 2 * k) * ((m : ℤ) + 3 - 2 * k)))
  have q0 : (F m k : ℚ) = F (m + 1) k * (((m : ℚ) + 1 - 2 * k) * ((m : ℚ) + 2 - 2 * k)) /
      (2 * ((m : ℚ) + 1) * (2 * m - 4 * k + 3)) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) n3)]
    exact_mod_cast (by linear_combination -e0 :
      F m k * (2 * ((m : ℤ) + 1) * (2 * m - 4 * k + 3)) =
        F (m + 1) k * (((m : ℤ) + 1 - 2 * k) * ((m : ℤ) + 2 - 2 * k)))
  have qy : (F (m + 4) (k + 1) : ℚ) =
      ((m : ℚ) + 4 - 2 * k) ^ 2 * (((m : ℚ) + 4 - 2 * k) ^ 2 - 1) * F (m + 4) k /
        (2 * (2 * (k : ℚ) + 2) * ((k : ℚ) + 2) * ((2 * m - 4 * k + 9) * (2 * m - 4 * k + 7))) := by
    rw [eq_div_iff (mul_ne_zero (by positivity) (mul_ne_zero n9 n7))]
    exact_mod_cast (by linear_combination ey :
      F (m + 4) (k + 1) * (2 * (2 * (k : ℤ) + 2) * ((k : ℤ) + 2) * ((2 * m - 4 * k + 9) * (2 * m - 4 * k + 7))) =
        ((m : ℤ) + 4 - 2 * k) ^ 2 * (((m : ℤ) + 4 - 2 * k) ^ 2 - 1) * F (m + 4) k)
  have n5' : (2 * (m : ℚ) - 4 * ((k + 1 : ℕ) : ℚ) + 9) = 2 * m - 4 * k + 5 := by push_cast; ring
  have n3' : (2 * (m : ℚ) - 4 * ((k + 1 : ℕ) : ℚ) + 7) = 2 * m - 4 * k + 3 := by push_cast; ring
  simp only [G]
  rw [n5', n3', q0, q1, q2, q3, qy]
  simp only [cp, t0, t1, t2, t3, t4, p0, p1, p2, p3]
  push_cast
  field_simp
  ring

/-- The telescoper annihilates the sum. -/
theorem rec_T (m : ℕ) :
    t0 m * S m + t1 m * S (m + 1) + t2 m * S (m + 2) + t3 m * S (m + 3) + t4 m * S (m + 4) = 0 := by
  have ext : ∀ n, n ≤ m + 4 → (S n : ℚ) = ∑ k ∈ Finset.range (m + 5), (F n k : ℚ) := by
    intro n hn
    rw [S, Int.cast_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun k _ hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have g0 : G m 0 = 0 := by simp [G, cp]
  have g1 : G m (m + 5) = 0 := by
    rw [G, F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hq : (t0 m : ℚ) * S m + t1 m * S (m + 1) + t2 m * S (m + 2) + t3 m * S (m + 3) + t4 m * S (m + 4) = 0 := by
    rw [ext m (by omega), ext (m + 1) (by omega), ext (m + 2) (by omega), ext (m + 3) (by omega),
      ext (m + 4) le_rfl, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun k _ => cert m k), Finset.sum_range_sub (G m), g0, g1, sub_zero]
  exact_mod_cast hq

/-! ### M annihilates the sum, and Mathar's operator is a left multiple of M -/

/-- M at m. -/
def e (m : ℕ) : ℤ := p0 m * S m + p1 m * S (m + 1) + p2 m * S (m + 2) + p3 m * S (m + 3)

lemma e_succ (m : ℕ) : (4 * (m : ℤ) + 15) * ((m : ℤ) + 5) * e (m + 1) = 2 * ((m : ℤ) + 3) * (4 * m + 19) * e m := by
  have h := rec_T m
  simp only [e, t0, t1, t2, t3, t4] at h ⊢
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 3 = m + 4 from rfl]
  linear_combination h

lemma e_zero : e 0 = 0 := by
  decide +kernel

lemma e_eq_zero : ∀ m, e m = 0
  | 0 => e_zero
  | m + 1 => by
    have h := e_succ m
    rw [e_eq_zero m, mul_zero] at h
    have hne : (4 * (m : ℤ) + 15) * ((m : ℤ) + 5) ≠ 0 := by positivity
    exact (mul_eq_zero.1 h).resolve_left hne

/-- Mathar's coefficients at n = m + 4, for a(m), ..., a(m+4). -/
def c0 (m : ℕ) : ℤ := 144 * (-((m : ℤ) + 2)) * ((m : ℤ) + 1)
def c1 (m : ℕ) : ℤ := 48 * ((m : ℤ) + 2) ^ 2
def c2 (m : ℕ) : ℤ := 8 * (4 * ((m : ℤ) + 4) ^ 2 + 3 * ((m : ℤ) + 4) - 3)
def c3 (m : ℕ) : ℤ := 4 * (-3 * ((m : ℤ) + 4) ^ 2 - 8 * ((m : ℤ) + 4) - 3)
def c4 (m : ℕ) : ℤ := ((m : ℤ) + 7) * ((m : ℤ) + 6)

/-- Mathar's expression at n = m + 4. -/
def Lm (m : ℕ) : ℤ := c0 m * S m + c1 m * S (m + 1) + c2 m * S (m + 2) + c3 m * S (m + 3) + c4 m * S (m + 4)

lemma L_eq (m : ℕ) : (4 * (m : ℤ) + 21) * Lm m = e (m + 1) - 6 * e m := by
  simp only [Lm, e, c0, c1, c2, c3, c4, p0, p1, p2, p3]
  rw [show m + 1 + 1 = m + 2 from rfl, show m + 1 + 2 = m + 3 from rfl, show m + 1 + 3 = m + 4 from rfl]
  push_cast
  ring

theorem L_eq_zero (m : ℕ) : Lm m = 0 := by
  have h := L_eq m
  rw [e_eq_zero, e_eq_zero, mul_zero, sub_zero] at h
  have hne : (4 * (m : ℤ) + 21) ≠ 0 := by positivity
  exact (mul_eq_zero.1 h).resolve_left hne

/-! ### The recurrence -/

/-- Mathar's recurrence, for every n ≥ 4. -/
theorem conjecture :
    ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 3) * ((n : ℤ) + 2) * (a n : ℤ) + 4 * (-3 * (n : ℤ) ^ 2 - 8 * (n : ℤ) - 3) * (a (n - 1) : ℤ) +
      8 * (4 * (n : ℤ) ^ 2 + 3 * (n : ℤ) - 3) * (a (n - 2) : ℤ) + 48 * ((n : ℤ) - 2) ^ 2 * (a (n - 3) : ℤ) +
      144 * (-((n : ℤ) - 2)) * ((n : ℤ) - 3) * (a (n - 4) : ℤ) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := L_eq_zero m
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 4 = m by omega, a_eq_S, a_eq_S, a_eq_S, a_eq_S, a_eq_S]
  simp only [Lm, c0, c1, c2, c3, c4] at h
  push_cast
  linear_combination h

/-- Controls: the entry's data a(0..25). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 11 ∧ a 3 = 44 ∧ a 4 = 188 ∧ a 5 = 842 ∧ a 6 = 3911 ∧ a 7 = 18692 ∧ a 8
    = 91412 ∧ a 9 = 455540 ∧ a 10 = 2306028 ∧ a 11 = 11829424 ∧ a 12 = 61375408 ∧ a 13 = 321583108 ∧
    a 14 = 1699500055 ∧ a 15 = 9049714852 ∧ a 16 = 48513809796 ∧ a 17 = 261638920412 ∧ a 18 =
    1418673379052 ∧ a 19 = 7730011715760 ∧ a 20 = 42305916178288 ∧ a 21 = 232475082183544 ∧ a 22 =
    1282208011668988 ∧ a 23 = 7096065370945168 ∧ a 24 = 39394821683770960 ∧ a 25 =
    219341739839760912 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
  ?_, ?_, ?_, ?_⟩
  all_goals
    rw [← Int.natCast_inj, a_eq_S]
    decide +kernel

end OMA.S_oeis_a302186

theorem OMA.solution : type_of% @OMA.S_oeis_a302186.main :=
  OMA.S_oeis_a302186.conjecture
