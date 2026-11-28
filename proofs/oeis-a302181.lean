import OMAStatements.S_oeis_a302181

namespace OMA.S_oeis_a302181




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

/-- The walks of N steps from the point (h, y, z) that keep x ≥ 0 and end at the origin. -/
def cnt (N : ℕ) (h y z : ℤ) : ℕ :=
  (Finset.univ.filter (fun w : Fin N → Fin 6 =>
    (∀ t ≤ N, 0 ≤ h + (pt w t).1) ∧ h + (pt w N).1 = 0 ∧ y + (pt w N).2.1 = 0 ∧ z + (pt w N).2.2 = 0)).card

lemma a_eq_cnt (n : ℕ) : a n = cnt (2 * n) 0 0 0 := by
  simp only [a, cnt, zero_add, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

lemma cnt_neg (N : ℕ) {h : ℤ} (y z : ℤ) (hh : h < 0) : cnt N h y z = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hw
  have h0 := hw.1 0 (Nat.zero_le _)
  rw [pt_zero] at h0
  simp only [Prod.fst_zero, add_zero] at h0
  omega

lemma cond_cons {N : ℕ} (c : Fin 6) (w : Fin N → Fin 6) (h y z : ℤ) (hh : 0 ≤ h) :
    ((∀ t ≤ N + 1, 0 ≤ h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) t).1) ∧
      h + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).1 = 0 ∧
      y + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).2.1 = 0 ∧
      z + (pt (Fin.cons c w : Fin (N + 1) → Fin 6) (N + 1)).2.2 = 0) ↔
    ((∀ t ≤ N, 0 ≤ (h + (step c).1) + (pt w t).1) ∧ (h + (step c).1) + (pt w N).1 = 0 ∧
      (y + (step c).2.1) + (pt w N).2.1 = 0 ∧ (z + (step c).2.2) + (pt w N).2.2 = 0) := by
  rw [pt_cons]
  simp only [Prod.fst_add, Prod.snd_add, ← add_assoc]
  refine and_congr ⟨fun H t ht => ?_, fun H t ht => ?_⟩ Iff.rfl
  · have := H (t + 1) (by omega)
    rwa [pt_cons, Prod.fst_add, ← add_assoc] at this
  · rcases t with _ | t
    · rw [pt_zero, Prod.fst_zero, add_zero]
      exact hh
    · rw [pt_cons, Prod.fst_add, ← add_assoc]
      exact H t (by omega)

lemma cnt_succ_sum (N : ℕ) (h y z : ℤ) (hh : 0 ≤ h) :
    cnt (N + 1) h y z = ∑ c : Fin 6, cnt N (h + (step c).1) (y + (step c).2.1) (z + (step c).2.2) := by
  rw [cnt, Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin 6)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [cnt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact if_congr (cond_cons c w h y z hh) rfl rfl

lemma cnt_succ (N : ℕ) (h y z : ℤ) (hh : 0 ≤ h) :
    (cnt (N + 1) h y z : ℤ) = cnt N (h + 1) y z + cnt N (h - 1) y z + cnt N h (y + 1) z + cnt N h (y - 1) z +
      cnt N h y (z + 1) + cnt N h y (z - 1) := by
  rw [cnt_succ_sum N h y z hh, Fin.sum_univ_six]
  simp [step]
  ring_nf

/-! ### The z-steps: a binomial transform weighted by the ±1 walks back to 0 -/

/-- The z-steps form a ±1 walk from z back to 0, placed among the N steps. -/
def Tb (N : ℕ) (f : ℕ → ℤ) (z : ℤ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * bin1 (N - k) z

lemma Tb_succ (N : ℕ) (f : ℕ → ℤ) (z : ℤ) :
    Tb (N + 1) f z = Tb N (fun k => f (k + 1)) z + Tb N f (z + 1) + Tb N f (z - 1) := by
  have h1 : Tb (N + 1) f z = ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * bin1 (N - k) z +
      ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * bin1 (N - k) z + f 0 * bin1 (N + 1) z := by
    rw [Tb, Finset.sum_range_succ', ← Finset.sum_add_distrib]
    simp only [Nat.choose_succ_succ', Nat.add_sub_add_right, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_add,
      Nat.cast_one, one_mul, add_mul]
  have h2 : Tb N f (z + 1) + Tb N f (z - 1) =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * bin1 (N - k) z + f 0 * bin1 (N + 1) z := by
    rw [Tb, Tb, ← Finset.sum_add_distrib]
    have e : ∀ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f k * bin1 (N - k) (z + 1) +
        (N.choose k : ℤ) * f k * bin1 (N - k) (z - 1) = (N.choose k : ℤ) * f k * bin1 (N + 1 - k) z := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show N + 1 - k = N - k + 1 by omega, bin1]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [show N + 1 - (k + 1) = N - k by omega]
  have h3 : ∑ k ∈ Finset.range (N + 1), (N.choose (k + 1) : ℤ) * f (k + 1) * bin1 (N - k) z =
      ∑ k ∈ Finset.range N, (N.choose (k + 1) : ℤ) * f (k + 1) * bin1 (N - k) z := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero]
  have h4 : Tb N (fun k => f (k + 1)) z =
      ∑ k ∈ Finset.range (N + 1), (N.choose k : ℤ) * f (k + 1) * bin1 (N - k) z := rfl
  rw [h1, h3]
  linarith [h2, h4]

lemma cnt_zero (h y z : ℤ) (hh : -1 ≤ h) : (cnt 0 h y z : ℤ) = AB 0 h y * bin1 0 z := by
  have hc : cnt 0 h y z = if h = 0 ∧ y = 0 ∧ z = 0 then 1 else 0 := by
    rw [cnt, Finset.card_filter, Fintype.sum_unique]
    simp only [nonpos_iff_eq_zero, forall_eq, pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
    by_cases h0 : h = 0 <;> by_cases y0 : y = 0 <;> by_cases z0 : z = 0 <;> simp [h0, y0, z0]
  rw [hc]
  simp only [AB, P, bin1]
  split_ifs <;> omega

/-- The count from any start with x ≥ -1. -/
theorem cnt_eq (N : ℕ) : ∀ h y z : ℤ, -1 ≤ h → (cnt N h y z : ℤ) = Tb N (fun k => AB k h y) z := by
  induction N with
  | zero =>
    intro h y z hh
    rw [cnt_zero h y z hh]
    simp [Tb]
  | succ N ih =>
    intro h y z hh
    rcases eq_or_lt_of_le hh with e | hh'
    · rw [← e, cnt_neg _ _ _ (by norm_num), Nat.cast_zero]
      simp [Tb, AB_neg_one]
    · have h0 : 0 ≤ h := by omega
      have hs : Tb N (fun k => AB (k + 1) h y) z = Tb N (fun k => AB k (h + 1) y) z +
          Tb N (fun k => AB k (h - 1) y) z + Tb N (fun k => AB k h (y + 1)) z + Tb N (fun k => AB k h (y - 1)) z := by
        simp only [Tb, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by rw [AB_succ]; ring)
      rw [cnt_succ N h y z h0, ih (h + 1) y z (by omega), ih (h - 1) y z (by omega), ih h (y + 1) z hh,
        ih h (y - 1) z hh, ih h y (z + 1) hh, ih h y (z - 1) hh, Tb_succ, hs]

/-! ### The sum -/

/-- The summand: 2k steps on the x and y axes (a walk of type ab back to the origin) and 2n - 2k
z-steps (a ±1 walk back to 0), interleaved. -/
def F (n k : ℕ) : ℤ := ((2 * n).choose (2 * k) : ℤ) * w k * ((2 * n - 2 * k).choose (n - k) : ℤ)

/-- The sum over k. -/
def S (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), F n k

/-- The count of the entry is the sum. -/
theorem a_eq_S (n : ℕ) : (a n : ℤ) = S n := by
  rw [a_eq_cnt, cnt_eq (2 * n) 0 0 0 (by norm_num), Tb]
  have hz : ∀ k ∈ Finset.range (2 * (n + 1)), k ∉ Finset.range (2 * n + 1) →
      ((2 * n).choose k : ℤ) * AB k 0 0 * bin1 (2 * n - k) 0 = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega)) hz,
    sum_even (fun k => ((2 * n).choose k : ℤ) * AB k 0 0 * bin1 (2 * n - k) 0) (fun i => by simp [AB_odd]) (n + 1)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hb := bin1_choose (2 * n - 2 * i) (n - i)
  rw [show ((2 * n - 2 * i : ℕ) : ℤ) - 2 * ((n - i : ℕ) : ℤ) = 0 by
    push_cast [Nat.cast_sub (show 2 * i ≤ 2 * n by omega), Nat.cast_sub (show i ≤ n by omega)]; ring] at hb
  rw [AB_even, hb, F]

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

/-! ### The recurrence -/

/-- Mathar's recurrence, for every n ≥ 2. -/
theorem conjecture :
    ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) ^ 3 * (a n : ℤ) -
      2 * (2 * (n : ℤ) - 1) * (10 * (n : ℤ) ^ 2 + 10 * (n : ℤ) + 3) * (a (n - 1) : ℤ) +
      36 * (n : ℤ) * (2 * (n : ℤ) - 1) * (2 * (n : ℤ) - 3) * (a (n - 2) : ℤ) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := b_eq_zero m
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, a_eq_S, a_eq_S, a_eq_S]
  simp only [b, l0, l1, l2] at h
  push_cast
  linear_combination h

/-- Controls: the entry's data a(0..18). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 62 ∧ a 3 = 1065 ∧ a 4 = 21714 ∧ a 5 = 492366 ∧ a 6 = 12004740 ∧ a 7 =
    308559537 ∧ a 8 = 8255788970 ∧ a 9 = 227976044010 ∧ a 10 = 6457854821340 ∧ a 11 =
    186814834574550 ∧ a 12 = 5500292590186380 ∧ a 13 = 164387681345290500 ∧ a 14 =
    4976887208815547640 ∧ a 15 = 152378485941172462785 ∧ a 16 = 4711642301137121933850 ∧ a 17 =
    146964278352052950118770 ∧ a 18 = 4619875954522866283392300 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [← Int.natCast_inj, a_eq_S]
    decide +kernel

end OMA.S_oeis_a302181

theorem OMA.solution : type_of% @OMA.S_oeis_a302181.main :=
  OMA.S_oeis_a302181.conjecture
