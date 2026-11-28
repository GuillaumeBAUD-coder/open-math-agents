import OMAStatements.S_oeis_a268775

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix over the rows (first row, pair count 0 or 1); the empirical recurrence annihilates the state vector, checked on explicit tables by decide

namespace OMA.P268775

open OMA.S_oeis_a268775 PowerSeries Matrix

abbrev Row := Fin 2 → Fin 2

def h (r : Row) : ℕ := if (r 0 : ℕ) + (r 1 : ℕ) = 2 then 1 else 0

def vv (r s : Row) : ℕ :=
  (if (r 0 : ℕ) + (s 0 : ℕ) = 2 then 1 else 0) + (if (r 1 : ℕ) + (s 1 : ℕ) = 2 then 1 else 0)
def vd (r s : Row) : ℕ := if (r 0 : ℕ) + (s 1 : ℕ) = 2 then 1 else 0
def va (r s : Row) : ℕ := if (r 1 : ℕ) + (s 0 : ℕ) = 2 then 1 else 0

def v (r s : Row) : ℕ := vv r s + vd r s + va r s

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ b : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma pairs_zero (y : Fin 1 → Row) : pairsTotallingTwo 0 y = h (y 0) := by
  unfold pairsTotallingTwo h
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_one]
  simp

lemma horiz_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    (∑ i : Fin (m + 2), if ((Fin.cons r y : Fin (m + 2) → Row) i 0 : ℕ) +
      ((Fin.cons r y : Fin (m + 2) → Row) i 1 : ℕ) = 2 then 1 else 0) =
    h r + ∑ i : Fin (m + 1), if (y i 0 : ℕ) + (y i 1 : ℕ) = 2 then 1 else 0 := by
  rw [Fin.sum_univ_succ]
  simp [h]

lemma vert_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    (∑ p : Fin (m + 1) × Fin 2,
      if ((Fin.cons r y : Fin (m + 2) → Row) p.1.castSucc p.2 : ℕ) +
        ((Fin.cons r y : Fin (m + 2) → Row) p.1.succ p.2 : ℕ) = 2 then 1 else 0) =
    vv r (y 0) + ∑ p : Fin m × Fin 2,
      if (y p.1.castSucc p.2 : ℕ) + (y p.1.succ p.2 : ℕ) = 2 then 1 else 0 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fin.sum_univ_succ]
  congr 1

lemma diag_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    (∑ i : Fin (m + 1), if ((Fin.cons r y : Fin (m + 2) → Row) i.castSucc 0 : ℕ) +
      ((Fin.cons r y : Fin (m + 2) → Row) i.succ 1 : ℕ) = 2 then 1 else 0) =
    vd r (y 0) + ∑ i : Fin m, if (y i.castSucc 0 : ℕ) + (y i.succ 1 : ℕ) = 2 then 1 else 0 := by
  rw [Fin.sum_univ_succ]
  rfl

lemma anti_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    (∑ i : Fin (m + 1), if ((Fin.cons r y : Fin (m + 2) → Row) i.castSucc 1 : ℕ) +
      ((Fin.cons r y : Fin (m + 2) → Row) i.succ 0 : ℕ) = 2 then 1 else 0) =
    va r (y 0) + ∑ i : Fin m, if (y i.castSucc 1 : ℕ) + (y i.succ 0 : ℕ) = 2 then 1 else 0 := by
  rw [Fin.sum_univ_succ]
  rfl

lemma pairs_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    pairsTotallingTwo (m + 1) (Fin.cons r y) = h r + v r (y 0) + pairsTotallingTwo m y := by
  unfold pairsTotallingTwo
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    horiz_cons, vert_cons, diag_cons, anti_cons]
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
  [[1, 1, 1, 0, 0, 0, 0, 1],
   [3, 1, 1, 0, 1, 2, 2, 1],
   [5, 3, 3, 0, 6, 3, 3, 3],
   [11, 5, 5, 0, 15, 12, 12, 5],
   [21, 11, 11, 0, 44, 25, 25, 11]]

def L (k : ℕ) (p : St) : ℤ :=
  (tab.getD k []).getD ((if p.1 then 4 else 0) + 2 * (p.2 0 : ℕ) + (p.2 1 : ℕ)) 0

lemma hV0 : V 0 = L 0 := by
  funext p
  obtain ⟨b, r⟩ := p
  simp only [V, N_zero]
  revert b r
  decide

lemma hM0 : M *ᵥ L 0 = L 1 := by decide

lemma hV1 : V 1 = L 1 := by rw [V_succ, hV0, hM0]

lemma hM1 : M *ᵥ L 1 = L 2 := by decide

lemma hV2 : V 2 = L 2 := by rw [V_succ, hV1, hM1]

lemma hM2 : M *ᵥ L 2 = L 3 := by decide

lemma hV3 : V 3 = L 3 := by rw [V_succ, hV2, hM2]

lemma hM3 : M *ᵥ L 3 = L 4 := by decide

lemma hV4 : V 4 = L 4 := by rw [V_succ, hV3, hM3]

def R (m : ℕ) : St → ℤ := V (m + 4) - ((2 : ℤ) • V (m + 3) + (3 : ℤ) • V (m + 2) + (-4 : ℤ) • V (m + 1) + (-4 : ℤ) • V (m + 0))

lemma R_succ (m : ℕ) : R (m + 1) = M *ᵥ R m := by
  have e : ∀ k, V (m + 1 + k) = M *ᵥ V (m + k) := fun k => by
    rw [show m + 1 + k = m + k + 1 by omega, V_succ]
  simp only [R, e, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul]

lemma R_base : R 0 = 0 := by
  rw [show R 0 = V 4 - ((2 : ℤ) • V 3 + (3 : ℤ) • V 2 + (-4 : ℤ) • V 1 + (-4 : ℤ) • V 0) from rfl, hV4, hV3, hV2, hV1, hV0]
  decide

lemma R_all : ∀ m : ℕ, 0 ≤ m → R m = 0 := by
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

lemma val1 : (a 1 : ℤ) = 4 := by
  rw [show a 1 = a (0 + 1) from rfl, a_succ, hV0]
  decide

lemma val2 : (a 2 : ℤ) = 11 := by
  rw [show a 2 = a (1 + 1) from rfl, a_succ, hV1]
  decide

lemma val3 : (a 3 : ℤ) = 26 := by
  rw [show a 3 = a (2 + 1) from rfl, a_succ, hV2]
  decide

lemma val4 : (a 4 : ℤ) = 65 := by
  rw [show a 4 = a (3 + 1) from rfl, a_succ, hV3]
  decide

theorem rec_thm : ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) - 4 * a (n - 4) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 = m + 4 + 1 by omega,
    show m + 5 - 1 = m + 3 + 1 by omega,
    show m + 5 - 2 = m + 2 + 1 by omega,
    show m + 5 - 3 = m + 1 + 1 by omega,
    show m + 5 - 4 = m + 0 + 1 by omega]
  simp only [a_succ]
  have hs : ∑ p : St, R (m + 0) p = 0 := by rw [R_all (m + 0) (by omega)]; simp
  simp only [R, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_assoc,
    Nat.reduceAdd, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  linear_combination hs

lemma gf_gen (f : ℕ → ℚ)
    (h0 : f 0 = 0) (h1 : f 1 = 4) (h2 : f 2 = 11) (h3 : f 3 = 26) (h4 : f 4 = 65)
    (hq : ∀ n : ℕ, 5 ≤ n → f n = 2 * f (n - 1) + 3 * f (n - 2) - 4 * f (n - 3) - 4 * f (n - 4)) :
    PowerSeries.mk f * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2) = X * (4 + 3 * X - 8 * X ^ 2 - 4 * X ^ 3) := by
  have hl : PowerSeries.mk f * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2) =
      PowerSeries.mk f - C (2 : ℚ) * (PowerSeries.mk f * X ^ 1) - C (3 : ℚ) * (PowerSeries.mk f * X ^ 2) + C (4 : ℚ) * (PowerSeries.mk f * X ^ 3) + C (4 : ℚ) * (PowerSeries.mk f * X ^ 4) := by
    try simp only [map_ofNat]
    ring
  have hr : (X * (4 + 3 * X - 8 * X ^ 2 - 4 * X ^ 3) : PowerSeries ℚ) =
      C (4 : ℚ) * X ^ 1 + C (3 : ℚ) * X ^ 2 - C (8 : ℚ) * X ^ 3 - C (4 : ℚ) * X ^ 4 := by
    try simp only [map_ofNat]
    ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_X_pow,
    coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3, h4] <;> norm_num
  · have hq' := hq n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have d1 : n - 1 ≠ 0 := by omega
    have e1 : n ≠ 1 := by omega
    have d2 : n - 2 ≠ 0 := by omega
    have e2 : n ≠ 2 := by omega
    have d3 : n - 3 ≠ 0 := by omega
    have e3 : n ≠ 3 := by omega
    have d4 : n - 4 ≠ 0 := by omega
    have e4 : n ≠ 4 := by omega
    simp only [c1, c2, c3, c4, d1, d2, d3, d4, e1, e2, e3, e4, if_true, if_false]
    linarith [hq']

theorem gf_thm : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2) =
      X * (4 + 3 * X - 8 * X ^ 2 - 4 * X ^ 3) :=
  gf_gen (fun n => (a n : ℚ))
    (by rw [show a 0 = 0 from rfl]; simp : ((a 0 : ℕ) : ℚ) = 0)
    (by exact_mod_cast val1 : ((a 1 : ℕ) : ℚ) = 4)
    (by exact_mod_cast val2 : ((a 2 : ℕ) : ℚ) = 11)
    (by exact_mod_cast val3 : ((a 3 : ℕ) : ℚ) = 26)
    (by exact_mod_cast val4 : ((a 4 : ℕ) : ℚ) = 65)
    (fun n hn => by exact_mod_cast rec_thm n hn)

def F (n : ℕ) : ℚ := ((-1) ^ (1 + n) + 2 ^ (2 + n) + ((-1) ^ n + 2 ^ (1 + n)) * n) / 3

lemma cf_gen (f : ℕ → ℚ)
    (h1 : f 1 = 4) (h2 : f 2 = 11) (h3 : f 3 = 26) (h4 : f 4 = 65)
    (hq : ∀ n : ℕ, 5 ≤ n → f n = 2 * f (n - 1) + 3 * f (n - 2) - 4 * f (n - 3) - 4 * f (n - 4)) :
    ∀ n : ℕ, 1 ≤ n → f n = F n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> norm_num [F, h1, h2, h3, h4]
    · rw [hq n h, ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega), ih (n - 3) (by omega) (by omega), ih (n - 4) (by omega) (by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      unfold F
      simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
      push_cast
      ring

theorem cf_thm : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = F n :=
  cf_gen (fun n => (a n : ℚ))
    (by exact_mod_cast val1 : ((a 1 : ℕ) : ℚ) = 4)
    (by exact_mod_cast val2 : ((a 2 : ℕ) : ℚ) = 11)
    (by exact_mod_cast val3 : ((a 3 : ℕ) : ℚ) = 26)
    (by exact_mod_cast val4 : ((a 4 : ℕ) : ℚ) = 65)
    (fun n hn => by exact_mod_cast rec_thm n hn)

theorem extra_thm :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = ((-1) ^ (1 + n) + 2 ^ (2 + n) + ((-1) ^ n + 2 ^ (1 + n)) * n) / 3) := by
  have hcf := cf_thm
  exact hcf

theorem main_proof :
    (∀ n : ℕ, 5 ≤ n →
      (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 4 * a (n - 3) - 4 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2) =
      X * (4 + 3 * X - 8 * X ^ 2 - 4 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = ((-1) ^ (1 + n) + 2 ^ (2 + n) + ((-1) ^ n + 2 ^ (1 + n)) * n) / 3) :=
  ⟨rec_thm, gf_thm, extra_thm⟩

end OMA.P268775

theorem OMA.solution : type_of% @OMA.S_oeis_a268775.main := OMA.P268775.main_proof
