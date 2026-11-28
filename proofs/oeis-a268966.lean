import OMAStatements.S_oeis_a268966

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix over the rows (first row, pair count 0 or 1); the empirical recurrence annihilates the state vector, checked on explicit tables by decide

namespace OMA.P268966

open OMA.S_oeis_a268966 PowerSeries Matrix

abbrev Row := Fin 3 → Fin 3

def h (r : Row) : ℕ :=
  (if (r 0 : ℕ) + (r 1 : ℕ) = 2 then 1 else 0) + (if (r 1 : ℕ) + (r 2 : ℕ) = 2 then 1 else 0)

def va (r s : Row) : ℕ :=
  (if (r 1 : ℕ) + (s 0 : ℕ) = 2 then 1 else 0) + (if (r 2 : ℕ) + (s 1 : ℕ) = 2 then 1 else 0)

def v (r s : Row) : ℕ := va r s

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ b : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma pairs_zero (y : Fin 1 → Row) : pairsTotallingTwo 0 y = h (y 0) := by
  unfold pairsTotallingTwo h
  revert y
  decide

lemma horiz_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    (∑ p : Fin (m + 2) × Fin 2,
      if ((Fin.cons r y : Fin (m + 2) → Row) p.1 p.2.castSucc : ℕ) +
        ((Fin.cons r y : Fin (m + 2) → Row) p.1 p.2.succ : ℕ) = 2 then 1 else 0) =
    h r + ∑ p : Fin (m + 1) × Fin 2,
      if (y p.1 p.2.castSucc : ℕ) + (y p.1 p.2.succ : ℕ) = 2 then 1 else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_succ]
  congr 1

lemma anti_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    (∑ p : Fin (m + 1) × Fin 2,
      if ((Fin.cons r y : Fin (m + 2) → Row) p.1.castSucc p.2.succ : ℕ) +
        ((Fin.cons r y : Fin (m + 2) → Row) p.1.succ p.2.castSucc : ℕ) = 2 then 1 else 0) =
    va r (y 0) + ∑ p : Fin m × Fin 2,
      if (y p.1.castSucc p.2.succ : ℕ) + (y p.1.succ p.2.castSucc : ℕ) = 2 then 1 else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_succ]
  congr 1

lemma pairs_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    pairsTotallingTwo (m + 1) (Fin.cons r y) = h r + v r (y 0) + pairsTotallingTwo m y := by
  unfold pairsTotallingTwo
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    horiz_cons, anti_cons]
  unfold v
  ring

/-- Arrays of `m + 1` rows starting with row `r` and with exactly `j` pairs totalling. -/
def N (m : ℕ) (r : Row) (j : ℕ) : ℕ :=
  ∑ y : Fin (m + 1) → Row, if y 0 = r ∧ pairsTotallingTwo m y = j then 1 else 0

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ c : Row, ∑ y : Fin (m + 1) → Row, if y 0 = c then g y else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

lemma N_zero (r : Row) (j : ℕ) : N 0 r j = if h r = j then 1 else 0 := by
  unfold N
  rw [← (Equiv.funUnique (Fin 1) Row).symm.sum_comp]
  simp [pairs_zero, ite_and, Finset.sum_ite_eq']

lemma shift (m : ℕ) (s : Row) (c j : ℕ) :
    (∑ y : Fin (m + 1) → Row, if y 0 = s ∧ c + pairsTotallingTwo m y = j then 1 else 0) =
      if c ≤ j then N m s (j - c) else 0 := by
  unfold N
  split_ifs with hc
  · apply Finset.sum_congr rfl
    intro y _
    have : (c + pairsTotallingTwo m y = j ↔ pairsTotallingTwo m y = j - c) := by omega
    simp only [this]
  · apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    omega

lemma N_succ (m : ℕ) (r : Row) (j : ℕ) :
    N (m + 1) r j = ∑ s : Row, if h r + v r s ≤ j then N m s (j - (h r + v r s)) else 0 := by
  have e : N (m + 1) r j = ∑ s : Row, ∑ y : Fin (m + 1) → Row,
      if y 0 = s ∧ (h r + v r s) + pairsTotallingTwo m y = j then 1 else 0 := by
    unfold N
    rw [sum_cons]
    simp only [Fin.cons_zero, pairs_cons]
    rw [Finset.sum_eq_single r (by intro b' _ hb'; simp [hb']) (by simp)]
    simp only [true_and]
    rw [fiber]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = s <;> simp [hy]
  rw [e]
  apply Finset.sum_congr rfl
  intro s _
  exact shift m s _ j

abbrev St := Bool × Row

def c (j : ℕ) (r s : Row) : ℤ := if h r + v r s = j then 1 else 0

/-- The transfer matrix on (number of pairs so far is one, first row). -/
def M : Matrix St St ℤ := fun p q =>
  if p.1 = q.1 then c 0 p.2 q.2 else if p.1 then c 1 p.2 q.2 else 0

def V (m : ℕ) : St → ℤ := fun p => (N m p.2 (if p.1 then 1 else 0) : ℤ)

lemma key0 (m : ℕ) (r s : Row) :
    (((if h r + v r s ≤ 0 then N m s (0 - (h r + v r s)) else 0 : ℕ)) : ℤ) =
      c 0 r s * N m s 0 := by
  unfold c
  by_cases hw : h r + v r s = 0
  · simp [hw]
  · have : ¬ (h r + v r s ≤ 0) := by omega
    rw [if_neg this, if_neg hw]
    simp

lemma key1 (m : ℕ) (r s : Row) :
    (((if h r + v r s ≤ 1 then N m s (1 - (h r + v r s)) else 0 : ℕ)) : ℤ) =
      c 0 r s * N m s 1 + c 1 r s * N m s 0 := by
  unfold c
  rcases Nat.lt_trichotomy (h r + v r s) 1 with hw | hw | hw
  · have h0 : h r + v r s = 0 := by omega
    simp [h0]
  · simp [hw]
  · have a1 : ¬ (h r + v r s ≤ 1) := by omega
    have a2 : h r + v r s ≠ 0 := by omega
    have a3 : h r + v r s ≠ 1 := by omega
    rw [if_neg a1, if_neg a2, if_neg a3]
    simp

lemma V_succ (m : ℕ) : V (m + 1) = M *ᵥ V m := by
  funext p
  obtain ⟨b, r⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_bool]
  cases b
  · have e : V (m + 1) (false, r) = ∑ s, c 0 r s * (N m s 0 : ℤ) := by
      show ((N (m + 1) r 0 : ℕ) : ℤ) = _
      rw [N_succ, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun s _ => key0 m r s)
    rw [e]
    simp [V, M]
  · have e : V (m + 1) (true, r) = ∑ s, c 0 r s * (N m s 1 : ℤ) + ∑ s, c 1 r s * (N m s 0 : ℤ) := by
      show ((N (m + 1) r 1 : ℕ) : ℤ) = _
      rw [N_succ, Nat.cast_sum, Finset.sum_congr rfl (fun s _ => key1 m r s), Finset.sum_add_distrib]
    rw [e]
    simp [V, M]

def tab : List (List ℤ) :=
  [[1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0],
   [6, 6, 0, 6, 0, 6, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 6, 0, 6, 0, 6, 6, 9, 9, 4, 9, 4, 9, 0, 6, 6, 9, 9, 4, 6, 0, 6, 4, 9, 9, 6, 6, 0, 9, 4, 9, 4, 9, 9],
   [36, 36, 0, 36, 0, 36, 0, 0, 0, 36, 36, 0, 0, 0, 0, 0, 36, 36, 0, 0, 0, 36, 0, 36, 0, 36, 36, 102, 102, 24, 102, 24, 102, 0, 36, 36, 102, 102, 24, 36, 0, 36, 24, 102, 102, 36, 36, 0, 102, 24, 102, 24, 102, 102],
   [216, 216, 0, 216, 0, 216, 0, 0, 0, 216, 216, 0, 0, 0, 0, 0, 216, 216, 0, 0, 0, 216, 0, 216, 0, 216, 216, 900, 900, 144, 900, 144, 900, 0, 216, 216, 900, 900, 144, 216, 0, 216, 144, 900, 900, 216, 216, 0, 900, 144, 900, 144, 900, 900]]

def L (k : ℕ) (p : St) : ℤ :=
  (tab.getD k []).getD
    ((if p.1 then 27 else 0) + 9 * (p.2 0 : ℕ) + 3 * (p.2 1 : ℕ) + (p.2 2 : ℕ)) 0

lemma hV0 : V 0 = L 0 := by
  funext p
  obtain ⟨b, r⟩ := p
  simp only [V, N_zero]
  revert b r
  decide +kernel

lemma hM0 : M *ᵥ L 0 = L 1 := by decide +kernel

lemma hV1 : V 1 = L 1 := by rw [V_succ, hV0, hM0]

lemma hM1 : M *ᵥ L 1 = L 2 := by decide +kernel

lemma hV2 : V 2 = L 2 := by rw [V_succ, hV1, hM1]

lemma hM2 : M *ᵥ L 2 = L 3 := by decide +kernel

lemma hV3 : V 3 = L 3 := by rw [V_succ, hV2, hM2]

def R (m : ℕ) : St → ℤ := V (m + 2) - ((12 : ℤ) • V (m + 1) + (-36 : ℤ) • V (m + 0))

lemma R_succ (m : ℕ) : R (m + 1) = M *ᵥ R m := by
  have e : ∀ k, V (m + 1 + k) = M *ᵥ V (m + k) := fun k => by
    rw [show m + 1 + k = m + k + 1 by omega, V_succ]
  simp only [R, e, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]

lemma R_base : R 1 = 0 := by
  rw [show R 1 = V 3 - ((12 : ℤ) • V 2 + (-36 : ℤ) • V 1) from rfl, hV3, hV2, hV1]
  decide +kernel

lemma R_all : ∀ m : ℕ, 1 ≤ m → R m = 0 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact R_base
  | succ k _ ih => rw [R_succ, ih, Matrix.mulVec_zero]

lemma a_succ (m : ℕ) : (a (m + 1) : ℤ) = ∑ p : St, V m p := by
  have e : a (m + 1) = ∑ r : Row, (N m r 0 + N m r 1) := by
    show (Finset.univ.filter (fun x : Fin (m + 1) → Row => pairsTotallingTwo m x ≤ 1)).card = _
    unfold N
    rw [Finset.card_filter, fiber]
    apply Finset.sum_congr rfl
    intro c _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = c
    · simp only [hy, true_and, if_true]
      split_ifs <;> omega
    · simp [hy]
  rw [e]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, V]
  push_cast
  simp [Finset.sum_add_distrib, add_comm]

lemma val1 : (a 1 : ℤ) = 24 := by
  rw [show a 1 = a (0 + 1) from rfl, a_succ, hV0]
  decide +kernel

lemma val2 : (a 2 : ℤ) = 240 := by
  rw [show a 2 = a (1 + 1) from rfl, a_succ, hV1]
  decide +kernel

lemma val3 : (a 3 : ℤ) = 2016 := by
  rw [show a 3 = a (2 + 1) from rfl, a_succ, hV2]
  decide +kernel

theorem rec_thm : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 12 * a (n - 1) - 36 * a (n - 2) := by
  intro n hn
  rcases Nat.lt_or_ge n 4 with hsm | hsm
  · interval_cases n <;> simp only [Nat.reduceSub, val1, val2, val3] <;> norm_num
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 = m + 3 + 1 by omega,
    show m + 4 - 1 = m + 2 + 1 by omega,
    show m + 4 - 2 = m + 1 + 1 by omega]
  simp only [a_succ]
  have hs : ∑ p : St, R (m + 1) p = 0 := by rw [R_all (m + 1) (by omega)]; simp
  simp only [R, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_assoc,
    Nat.reduceAdd, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linear_combination hs

lemma gf_gen (f : ℕ → ℚ)
    (h0 : f 0 = 0) (h1 : f 1 = 24) (h2 : f 2 = 240)
    (hq : ∀ n : ℕ, 3 ≤ n → f n = 12 * f (n - 1) - 36 * f (n - 2)) :
    PowerSeries.mk f * (1 - 6 * X) ^ 2 = 24 * X * (1 - 2 * X) := by
  have hl : PowerSeries.mk f * (1 - 6 * X) ^ 2 =
      PowerSeries.mk f - C (12 : ℚ) * (PowerSeries.mk f * X ^ 1) + C (36 : ℚ) * (PowerSeries.mk f * X ^ 2) := by
    try simp only [map_ofNat]
    try ring
  have hr : (24 * X * (1 - 2 * X) : PowerSeries ℚ) =
      C (24 : ℚ) * X ^ 1 - C (48 : ℚ) * X ^ 2 := by
    try simp only [map_ofNat]
    try ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_X_pow,
    coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [h0, h1, h2] <;> norm_num
  · have hq' := hq n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have d1 : n - 1 ≠ 0 := by omega
    have e1 : n ≠ 1 := by omega
    have d2 : n - 2 ≠ 0 := by omega
    have e2 : n ≠ 2 := by omega
    simp only [c1, c2, d1, d2, e1, e2, if_true, if_false]
    linarith [hq']

theorem gf_thm : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X) ^ 2 =
      24 * X * (1 - 2 * X) :=
  gf_gen (fun n => (a n : ℚ))
    (by rw [show a 0 = 0 from rfl]; simp : ((a 0 : ℕ) : ℚ) = 0)
    (by exact_mod_cast val1 : ((a 1 : ℕ) : ℚ) = 24)
    (by exact_mod_cast val2 : ((a 2 : ℕ) : ℚ) = 240)
    (fun n hn => by exact_mod_cast rec_thm n hn)

def F (n : ℕ) : ℚ := 2 ^ (n + 2) * 3 ^ (n - 1) * (2 * n + 1)

lemma cf_gen (f : ℕ → ℚ)
    (h1 : f 1 = 24) (h2 : f 2 = 240)
    (hq : ∀ n : ℕ, 3 ≤ n → f n = 12 * f (n - 1) - 36 * f (n - 2)) :
    ∀ n : ℕ, 1 ≤ n → f n = F n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> norm_num [F, h1, h2]
    · rw [hq n h, ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      unfold F
      simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
      simp only [show k + 1 - 1 = k + 0 by omega, show k + 2 - 1 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega]
      push_cast
      ring

theorem cf_thm : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = F n :=
  cf_gen (fun n => (a n : ℚ))
    (by exact_mod_cast val1 : ((a 1 : ℕ) : ℚ) = 24)
    (by exact_mod_cast val2 : ((a 2 : ℕ) : ℚ) = 240)
    (fun n hn => by exact_mod_cast rec_thm n hn)

theorem extra_thm :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = 2 ^ (n + 2) * 3 ^ (n - 1) * (2 * n + 1)) := by
  have hcf := cf_thm
  exact hcf

theorem main_proof :
    (∀ n : ℕ, 3 ≤ n →
      (a n : ℤ) = 12 * a (n - 1) - 36 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X) ^ 2 =
      24 * X * (1 - 2 * X)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = 2 ^ (n + 2) * 3 ^ (n - 1) * (2 * n + 1)) :=
  ⟨rec_thm, gf_thm, extra_thm⟩

end OMA.P268966

theorem OMA.solution : type_of% @OMA.S_oeis_a268966.main := OMA.P268966.main_proof
