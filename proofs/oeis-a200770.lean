import OMAStatements.S_oeis_a200770

-- Problem: A200770: Number of nX1 0..2 arrays with every row and column running average
-- nondecreasing rightwards and downwards, and the number of instances of each value within one
-- of each other.
-- Credit: @EmadY (the owner of the agent is credited as the solver)
--
-- Proof idea. The running average does not decrease from row p - 1 to row p exactly when the
-- sum of the first p entries is at most p * w_p. So a 0 needs only zeros above it, a 1 needs at
-- most as many twos as zeros above it, and a 2 is always allowed. Appending one letter at a time,
-- the number N(z, o, t) of such words with z zeros, o ones and t twos satisfies a Pascal-type
-- recursion with solution N(z, o, t) = C(o + min(z, t), o). Summing over the balanced counts,
--   a(3m) = C(2m, m),  a(3m+1) = 2 C(2m, m) + C(2m+1, m+1),  a(3m+2) = 3 C(2m+1, m+1),
-- so a(k+1)/a(k) is (4m+3)/(m+1), 3(2m+1)/(4m+3) or 2/3 according as k = 3m, 3m+1 or 3m+2,
-- and the recurrence reduces to a polynomial identity once these ratios are substituted.

namespace OMA.S_oeis_a200770

open Nat


/-! ## The running average condition, locally -/

/-- The sum of the entries above row `p`. -/
def pre {n : ℕ} (w : Fin n → Fin 3) (p : Fin n) : ℕ :=
  ∑ k : Fin n, if k < p then (w k).val else 0

/-- Each entry is at least the average of the entries above it. -/
def Loc {n : ℕ} (w : Fin n → Fin 3) : Prop := ∀ p : Fin n, pre w p ≤ p.val * (w p).val

instance {n : ℕ} (w : Fin n → Fin 3) : Decidable (Loc w) := by unfold Loc; infer_instance

lemma sum_le_pred {n : ℕ} (w : Fin n → Fin 3) (i j : Fin n) (h : i.val + 1 = j.val) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ i), ((w k).val : ℚ)) = (pre w j : ℚ) := by
  rw [Finset.sum_filter, pre]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk : k ≤ i ↔ k < j := by rw [Fin.le_def, Fin.lt_def]; omega
  by_cases h' : k < j
  · rw [if_pos (hk.2 h'), if_pos h']
  · rw [if_neg (fun h'' => h' (hk.1 h'')), if_neg h']

lemma sum_le_self {n : ℕ} (w : Fin n → Fin 3) (j : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), ((w k).val : ℚ)) =
      (pre w j : ℚ) + (w j).val := by
  rw [Finset.sum_filter, pre]
  push_cast
  have e : ∀ k : Fin n, (if k ≤ j then ((w k).val : ℚ) else 0) =
      (if k < j then ((w k).val : ℚ) else 0) + (if k = j then ((w k).val : ℚ) else 0) := by
    intro k
    rcases lt_trichotomy k j with h | h | h
    · simp [h, h.le, h.ne]
    · simp [h]
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  rw [Finset.sum_congr rfl (fun k _ => e k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma avg_iff {n : ℕ} (w : Fin n → Fin 3) :
    (∀ i j : Fin n, i.val + 1 = j.val → runAvg w i ≤ runAvg w j) ↔ Loc w := by
  have key : ∀ i j : Fin n, i.val + 1 = j.val →
      (runAvg w i ≤ runAvg w j ↔ pre w j ≤ j.val * (w j).val) := by
    intro i j h
    unfold runAvg
    rw [sum_le_pred w i j h, sum_le_self w j]
    have hi : (0 : ℚ) < (i.val : ℚ) + 1 := by positivity
    have hj : (0 : ℚ) < (j.val : ℚ) + 1 := by positivity
    rw [div_le_div_iff₀ hi hj]
    have hji : (j.val : ℚ) = i.val + 1 := by exact_mod_cast h.symm
    rw [hji]
    constructor
    · intro hle
      have : ((pre w j : ℕ) : ℚ) ≤ ((i.val : ℚ) + 1) * ((w j).val : ℚ) := by nlinarith
      rw [← h]; exact_mod_cast this
    · intro hle
      have : ((pre w j : ℕ) : ℚ) ≤ ((i.val : ℚ) + 1) * ((w j).val : ℚ) := by
        rw [← h] at hle; exact_mod_cast hle
      nlinarith
  constructor
  · intro H p
    rcases Nat.eq_zero_or_pos p.val with hp | hp
    · have : pre w p = 0 :=
        Finset.sum_eq_zero (fun k _ => if_neg (by rw [Fin.lt_def]; omega))
      rw [this]; exact Nat.zero_le _
    · exact (key ⟨p.val - 1, by omega⟩ p (by simp; omega)).1 (H _ _ (by simp; omega))
  · intro H i j h
    exact (key i j h).2 (H j)

/-! ## Appending a letter -/

lemma sum_snoc {L : ℕ} (f : (Fin (L + 1) → Fin 3) → ℕ) :
    ∑ w : Fin (L + 1) → Fin 3, f w = ∑ x : Fin 3, ∑ w : Fin L → Fin 3, f (Fin.snoc w x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin 3)) _ _ (fun _ => rfl)).symm

lemma numOcc_snoc {L : ℕ} (w : Fin L → Fin 3) (x v : Fin 3) :
    numOcc (Fin.snoc w x : Fin (L + 1) → Fin 3) v = numOcc w v + if x = v then 1 else 0 := by
  unfold numOcc
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma pre_snoc_castSucc {L : ℕ} (w : Fin L → Fin 3) (x : Fin 3) (q : Fin L) :
    pre (Fin.snoc w x : Fin (L + 1) → Fin 3) q.castSucc = pre w q := by
  unfold pre
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_castSucc_iff, Fin.snoc_castSucc]
  rw [if_neg (not_lt.mpr (Fin.castSucc_lt_last q).le), add_zero]

lemma pre_snoc_last {L : ℕ} (w : Fin L → Fin 3) (x : Fin 3) :
    pre (Fin.snoc w x : Fin (L + 1) → Fin 3) (Fin.last L) = ∑ k : Fin L, (w k).val := by
  unfold pre
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_lt_last, if_true, Fin.snoc_castSucc, lt_self_iff_false, if_false,
    add_zero]

lemma sum_val {L : ℕ} (w : Fin L → Fin 3) :
    ∑ k : Fin L, (w k).val = numOcc w 1 + 2 * numOcc w 2 := by
  unfold numOcc
  rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  generalize w k = y; fin_cases y <;> rfl

lemma numOcc_total {L : ℕ} (w : Fin L → Fin 3) :
    numOcc w 0 + numOcc w 1 + numOcc w 2 = L := by
  unfold numOcc
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  calc _ = ∑ _k : Fin L, 1 := Finset.sum_congr rfl (fun k _ => by
          generalize w k = x; fin_cases x <;> rfl)
    _ = L := by simp

lemma loc_snoc {L : ℕ} (w : Fin L → Fin 3) (x : Fin 3) :
    Loc (Fin.snoc w x : Fin (L + 1) → Fin 3) ↔
      Loc w ∧ numOcc w 1 + 2 * numOcc w 2 ≤ L * x.val := by
  unfold Loc
  rw [Fin.forall_fin_succ']
  simp only [pre_snoc_castSucc, pre_snoc_last, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last, sum_val]

/-! ## Counting by numbers of letters -/

/-- The number of locally valid words of length `L` with `z` zeros, `o` ones and `t` twos. -/
def N (L z o t : ℕ) : ℕ :=
  ∑ w : Fin L → Fin 3,
    if Loc w ∧ numOcc w 0 = z ∧ numOcc w 1 = o ∧ numOcc w 2 = t then 1 else 0

lemma ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then 1 else 0 : ℕ) = if Q then 1 else 0 := by
  by_cases hQ : Q
  · rw [if_pos (h.2 hQ), if_pos hQ]
  · rw [if_neg (fun hP => hQ (h.1 hP)), if_neg hQ]

lemma N_zero : N 0 0 0 0 = 1 := by
  simp [N, Loc, numOcc]

lemma N_succ (L z o t : ℕ) : N (L + 1) z o t =
    (if o = 0 ∧ t = 0 ∧ z ≠ 0 then N L (z - 1) 0 0 else 0) +
    (if o ≠ 0 ∧ t ≤ z then N L z (o - 1) t else 0) +
    (if t ≠ 0 then N L z o (t - 1) else 0) := by
  unfold N
  rw [sum_snoc, Fin.sum_univ_three]
  have h01 : ((0 : Fin 3) = 1) = False := eq_false (by decide)
  have h02 : ((0 : Fin 3) = 2) = False := eq_false (by decide)
  have h10 : ((1 : Fin 3) = 0) = False := eq_false (by decide)
  have h12 : ((1 : Fin 3) = 2) = False := eq_false (by decide)
  have h20 : ((2 : Fin 3) = 0) = False := eq_false (by decide)
  have h21 : ((2 : Fin 3) = 1) = False := eq_false (by decide)
  simp only [loc_snoc, numOcc_snoc, h01, h02, h10, h12, h20, h21, if_true, if_false, add_zero,
    Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, mul_one]
  congr 1
  congr 1
  · split_ifs with h
    · refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
      have := numOcc_total w
      constructor
      · rintro ⟨⟨hl, hs⟩, h0, h1, h2⟩; exact ⟨hl, by omega, by omega, by omega⟩
      · rintro ⟨hl, h0, h1, h2⟩; exact ⟨⟨hl, by omega⟩, by omega, by omega, by omega⟩
    · refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
      rintro ⟨⟨hl, hs⟩, h0, h1, h2⟩
      exact h ⟨by omega, by omega, by omega⟩
  · split_ifs with h
    · refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
      have := numOcc_total w
      constructor
      · rintro ⟨⟨hl, hs⟩, h0, h1, h2⟩; exact ⟨hl, by omega, by omega, by omega⟩
      · rintro ⟨hl, h0, h1, h2⟩; exact ⟨⟨hl, by omega⟩, by omega, by omega, by omega⟩
    · refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
      rintro ⟨⟨hl, hs⟩, h0, h1, h2⟩
      have := numOcc_total w
      exact h ⟨by omega, by omega⟩
  · split_ifs with h
    · refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
      have := numOcc_total w
      constructor
      · rintro ⟨⟨hl, hs⟩, h0, h1, h2⟩; exact ⟨hl, by omega, by omega, by omega⟩
      · rintro ⟨hl, h0, h1, h2⟩; exact ⟨⟨hl, by omega⟩, by omega, by omega, by omega⟩
    · refine Finset.sum_eq_zero (fun w _ => if_neg ?_)
      rintro ⟨⟨hl, hs⟩, h0, h1, h2⟩
      exact h (by omega)

lemma N_eq : ∀ L z o t : ℕ, z + o + t = L → N L z o t = (o + min z t).choose o
  | 0, z, o, t, h => by
    obtain ⟨rfl, rfl, rfl⟩ : z = 0 ∧ o = 0 ∧ t = 0 := ⟨by omega, by omega, by omega⟩
    simp [N_zero]
  | L + 1, z, o, t, h => by
    rw [N_succ]
    rcases Nat.eq_zero_or_pos o with ho | ho <;> rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ho; subst ht
      rw [if_pos ⟨rfl, rfl, by omega⟩, if_neg (by omega), if_neg (by omega),
        N_eq L (z - 1) 0 0 (by omega)]
      simp
    · subst ho
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), N_eq L z 0 (t - 1) (by omega)]
      simp
    · subst ht
      rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), N_eq L z (o - 1) 0 (by omega)]
      simp
    · rcases le_or_gt t z with htz | htz
      · rw [if_neg (by omega), if_pos ⟨by omega, htz⟩, if_pos (by omega),
          N_eq L z (o - 1) t (by omega), N_eq L z o (t - 1) (by omega),
          min_eq_right htz, min_eq_right (by omega : t - 1 ≤ z)]
        obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have := Nat.choose_succ_succ' (o' + t' + 1) o'
        rw [show o' + 1 + (t' + 1) = o' + t' + 1 + 1 by ring, this,
          show o' + (t' + 1) = o' + t' + 1 by ring, show o' + 1 + t' = o' + t' + 1 by ring, zero_add]
      · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), N_eq L z o (t - 1) (by omega),
          min_eq_left htz.le, min_eq_left (by omega : z ≤ t - 1), zero_add, zero_add]

/-! ## A200770 as a sum over the numbers of letters -/

lemma forall_fin3 (f : Fin 3 → ℕ) : (∀ u v : Fin 3, f u ≤ f v + 1) ↔
    (f 0 ≤ f 1 + 1 ∧ f 1 ≤ f 0 + 1 ∧ f 0 ≤ f 2 + 1 ∧ f 2 ≤ f 0 + 1 ∧
      f 1 ≤ f 2 + 1 ∧ f 2 ≤ f 1 + 1) := by
  constructor
  · intro h; exact ⟨h 0 1, h 1 0, h 0 2, h 2 0, h 1 2, h 2 1⟩
  · rintro ⟨h01, h10, h02, h20, h12, h21⟩ u v
    fin_cases u <;> fin_cases v <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      omega

/-- The numbers of instances `p`, `q`, `r` are within one of each other. -/
def Bal3 (p q r : ℕ) : Prop :=
  p ≤ q + 1 ∧ q ≤ p + 1 ∧ p ≤ r + 1 ∧ r ≤ p + 1 ∧ q ≤ r + 1 ∧ r ≤ q + 1

instance (p q r : ℕ) : Decidable (Bal3 p q r) := by unfold Bal3; infer_instance

lemma a_eq_sum (n : ℕ) : a n = ∑ w : Fin n → Fin 3,
    if Loc w ∧ Bal3 (numOcc w 0) (numOcc w 1) (numOcc w 2) then 1 else 0 := by
  unfold a
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
  unfold Valid Bal3
  rw [avg_iff, forall_fin3]

lemma sum_split3 {L : ℕ} (P : ℕ → ℕ → ℕ → Prop) [∀ p q r, Decidable (P p q r)]
    (p₁ q₁ r₁ p₂ q₂ r₂ p₃ q₃ r₃ : ℕ)
    (h : ∀ p q r, p + q + r = L → (if P p q r then 1 else 0 : ℕ) =
      (if p = p₁ ∧ q = q₁ ∧ r = r₁ then 1 else 0) + (if p = p₂ ∧ q = q₂ ∧ r = r₂ then 1 else 0) +
        (if p = p₃ ∧ q = q₃ ∧ r = r₃ then 1 else 0)) :
    (∑ w : Fin L → Fin 3, if Loc w ∧ P (numOcc w 0) (numOcc w 1) (numOcc w 2) then 1 else 0) =
      N L p₁ q₁ r₁ + N L p₂ q₂ r₂ + N L p₃ q₃ r₃ := by
  unfold N
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hl : Loc w
  · simp only [hl, true_and]; exact h _ _ _ (numOcc_total w)
  · simp only [hl, false_and, if_false, add_zero]

lemma sum_split1 {L : ℕ} (P : ℕ → ℕ → ℕ → Prop) [∀ p q r, Decidable (P p q r)]
    (p₁ q₁ r₁ : ℕ)
    (h : ∀ p q r, p + q + r = L → (P p q r ↔ p = p₁ ∧ q = q₁ ∧ r = r₁)) :
    (∑ w : Fin L → Fin 3, if Loc w ∧ P (numOcc w 0) (numOcc w 1) (numOcc w 2) then 1 else 0) =
      N L p₁ q₁ r₁ := by
  unfold N
  refine Finset.sum_congr rfl (fun w _ => ite_iff ?_)
  rw [h _ _ _ (numOcc_total w)]

lemma a_3m (m : ℕ) : a (3 * m) = (2 * m).choose m := by
  rw [a_eq_sum, sum_split1 Bal3 m m m (fun p q r hs => by unfold Bal3; omega),
    N_eq _ _ _ _ (by ring), show m + min m m = 2 * m by omega]

lemma a_3m1 (m : ℕ) : a (3 * m + 1) = 2 * (2 * m).choose m + (2 * m + 1).choose (m + 1) := by
  rw [a_eq_sum, sum_split3 Bal3 (m + 1) m m m (m + 1) m m m (m + 1) (fun p q r hs => by
      by_cases h : Bal3 p q r
      · rw [if_pos h]; unfold Bal3 at h; split_ifs <;> omega
      · rw [if_neg h]; unfold Bal3 at h; split_ifs <;> omega),
    N_eq _ _ _ _ (by ring), N_eq _ _ _ _ (by ring), N_eq _ _ _ _ (by ring),
    show m + min (m + 1) m = 2 * m by omega, show m + 1 + min m m = 2 * m + 1 by omega,
    show m + min m (m + 1) = 2 * m by omega]
  ring

lemma a_3m2 (m : ℕ) : a (3 * m + 2) = 3 * (2 * m + 1).choose (m + 1) := by
  rw [a_eq_sum, sum_split3 Bal3 (m + 1) (m + 1) m (m + 1) m (m + 1) m (m + 1) (m + 1)
      (fun p q r hs => by
        by_cases h : Bal3 p q r
        · rw [if_pos h]; unfold Bal3 at h; split_ifs <;> omega
        · rw [if_neg h]; unfold Bal3 at h; split_ifs <;> omega),
    N_eq _ _ _ _ (by ring), N_eq _ _ _ _ (by ring), N_eq _ _ _ _ (by ring),
    show m + 1 + min (m + 1) m = 2 * m + 1 by omega, show m + min (m + 1) (m + 1) = 2 * m + 1 by omega,
    show m + 1 + min m (m + 1) = 2 * m + 1 by omega, ← Nat.choose_symm_half m]
  ring

/-! ## Ratios of consecutive terms -/

lemma hb1 (m : ℕ) : ((m : ℚ) + 1) * ((2 * m + 1).choose (m + 1) : ℚ) =
    (2 * m + 1) * ((2 * m).choose m : ℚ) := by
  have := Nat.add_one_mul_choose_eq (2 * m) m
  have h' : ((2 * m + 1 : ℕ) : ℚ) * ((2 * m).choose m : ℚ) =
      ((2 * m + 1).choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) := by exact_mod_cast this
  push_cast at h'
  linarith

lemma hb3 (m : ℕ) : ((2 * (m + 1)).choose (m + 1) : ℚ) * ((m : ℚ) + 1) =
    (2 * m + 2) * ((2 * m + 1).choose (m + 1) : ℚ) := by
  have := Nat.add_one_mul_choose_eq (2 * m + 1) m
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, ← Nat.choose_symm_half m] at this
  have h' : ((2 * (m + 1) : ℕ) : ℚ) * ((2 * m + 1).choose (m + 1) : ℚ) =
      ((2 * (m + 1)).choose (m + 1) : ℚ) * ((m + 1 : ℕ) : ℚ) := by exact_mod_cast this
  push_cast at h'
  linarith

lemma q0 (m k k' : ℕ) (hk : k = 3 * m) (hk' : k' = 3 * m + 1) :
    (a k' : ℚ) = (4 * m + 3) / (m + 1) * a k := by
  subst hk hk'
  rw [a_3m1, a_3m]
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hm]
  push_cast
  linear_combination hb1 m

lemma q1 (m k k' : ℕ) (hk : k = 3 * m + 1) (hk' : k' = 3 * m + 2) :
    (a k' : ℚ) = 3 * (2 * m + 1) / (4 * m + 3) * a k := by
  subst hk hk'
  rw [a_3m2, a_3m1]
  have hm : (4 * m : ℚ) + 3 ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hm]
  push_cast
  linear_combination 6 * hb1 m

lemma q2 (m k k' : ℕ) (hk : k = 3 * m + 2) (hk' : k' = 3 * m + 3) :
    (a k' : ℚ) = 2 / 3 * a k := by
  subst hk hk'
  rw [show 3 * m + 3 = 3 * (m + 1) by ring, a_3m, a_3m2]
  have hm : (m : ℚ) + 1 ≠ 0 := by positivity
  have hD : ((2 * (m + 1)).choose (m + 1) : ℚ) = 2 * ((2 * m + 1).choose (m + 1) : ℚ) :=
    mul_right_cancel₀ hm (by linear_combination hb3 m)
  push_cast
  rw [hD]
  ring

/-! ## The recurrence -/

lemma rec_q (n : ℕ) (hn : 5 ≤ n) :
    ((n : ℚ) + 2) * (2770 * (n : ℚ) - 4893) * (a n : ℚ)
      + 3 * (1090 * (n : ℚ) ^ 2 - 4919 * (n : ℚ) + 1654) * (a (n - 1) : ℚ)
      + 4686 * (a (n - 2) : ℚ)
      + 2 * (-5540 * (n : ℚ) ^ 2 + 7016 * (n : ℚ) + 17127) * (a (n - 3) : ℚ)
      - 6 * (1090 * (n : ℚ) - 2739) * (2 * (n : ℚ) - 7) * (a (n - 4) : ℚ) = 0 := by
  obtain ⟨m, rfl | rfl | rfl⟩ : ∃ m, n = 3 * m + 5 ∨ n = 3 * m + 6 ∨ n = 3 * m + 7 :=
    ⟨(n - 5) / 3, by omega⟩
  · have e5 := q1 (m + 1) (3 * m + 4) (3 * m + 5) (by ring) (by ring)
    have e4 := q0 (m + 1) (3 * m + 3) (3 * m + 4) (by ring) (by ring)
    have e3 := q2 m (3 * m + 2) (3 * m + 3) rfl rfl
    have e2 := q1 m (3 * m + 1) (3 * m + 2) rfl rfl
    simp only [show 3 * m + 5 - 1 = 3 * m + 4 by omega, show 3 * m + 5 - 2 = 3 * m + 3 by omega,
      show 3 * m + 5 - 3 = 3 * m + 2 by omega, show 3 * m + 5 - 4 = 3 * m + 1 by omega]
    rw [e5, e4, e3, e2]
    push_cast
    have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h3 : 4 * (m : ℚ) + 3 ≠ 0 := by positivity
    have h4 : 4 * ((m : ℚ) + 1) + 3 ≠ 0 := by positivity
    field_simp
    ring
  · have e6 := q2 (m + 1) (3 * m + 5) (3 * m + 6) (by ring) (by ring)
    have e5 := q1 (m + 1) (3 * m + 4) (3 * m + 5) (by ring) (by ring)
    have e4 := q0 (m + 1) (3 * m + 3) (3 * m + 4) (by ring) (by ring)
    have e3 := q2 m (3 * m + 2) (3 * m + 3) rfl rfl
    simp only [show 3 * m + 6 - 1 = 3 * m + 5 by omega, show 3 * m + 6 - 2 = 3 * m + 4 by omega,
      show 3 * m + 6 - 3 = 3 * m + 3 by omega, show 3 * m + 6 - 4 = 3 * m + 2 by omega]
    rw [e6, e5, e4, e3]
    push_cast
    have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h4 : 4 * ((m : ℚ) + 1) + 3 ≠ 0 := by positivity
    field_simp
    ring
  · have e7 := q0 (m + 2) (3 * m + 6) (3 * m + 7) (by ring) (by ring)
    have e6 := q2 (m + 1) (3 * m + 5) (3 * m + 6) (by ring) (by ring)
    have e5 := q1 (m + 1) (3 * m + 4) (3 * m + 5) (by ring) (by ring)
    have e4 := q0 (m + 1) (3 * m + 3) (3 * m + 4) (by ring) (by ring)
    simp only [show 3 * m + 7 - 1 = 3 * m + 6 by omega, show 3 * m + 7 - 2 = 3 * m + 5 by omega,
      show 3 * m + 7 - 3 = 3 * m + 4 by omega, show 3 * m + 7 - 4 = 3 * m + 3 by omega]
    rw [e7, e6, e5, e4]
    push_cast
    have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
    have h3 : (m : ℚ) + 2 + 1 ≠ 0 := by positivity
    have h4 : 4 * ((m : ℚ) + 1) + 3 ≠ 0 := by positivity
    field_simp
    ring

theorem main_proof : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 2) * (2770 * (n : ℤ) - 4893) * (a n : ℤ)
      + 3 * (1090 * (n : ℤ) ^ 2 - 4919 * (n : ℤ) + 1654) * (a (n - 1) : ℤ)
      + 4686 * (a (n - 2) : ℤ)
      + 2 * (-5540 * (n : ℤ) ^ 2 + 7016 * (n : ℤ) + 17127) * (a (n - 3) : ℤ)
      - 6 * (1090 * (n : ℤ) - 2739) * (2 * (n : ℤ) - 7) * (a (n - 4) : ℤ) = 0 := by
  intro n hn
  have h := rec_q n hn
  exact_mod_cast h

end OMA.S_oeis_a200770

theorem OMA.solution : type_of% @OMA.S_oeis_a200770.main :=
  OMA.S_oeis_a200770.main_proof
