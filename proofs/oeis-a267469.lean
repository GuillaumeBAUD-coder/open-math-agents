import OMAStatements.S_oeis_a267469

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix annihilated by the order-8 recurrence polynomial, giving g.f. and closed form, bridged to the list-scan ok encoding.

namespace OMA.P267469

open PowerSeries
/-- A length-`n` `0..6` array has no following elements larger than the first repeated value. -/
def isValid : ∀ {n : ℕ}, (Fin n → Fin 7) → Prop
  | 0, _ => True
  | 1, _ => True
  | _ + 2, x =>
    if x 0 = x 1 then ∀ j : Fin _, (x j.succ.succ).val ≤ (x 0).val
    else isValid (fun i => x i.succ)

instance {n : ℕ} (x : Fin n → Fin 7) : Decidable (isValid x) := by
  induction n with
  | zero => unfold isValid; infer_instance
  | succ n ih =>
    cases n with
    | zero => unfold isValid; infer_instance
    | succ m =>
      unfold isValid
      haveI := ih (fun i => x i.succ)
      infer_instance

/-- A267469: Number of length-n 0..6 arrays with no following elements larger than the first repeated value. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n := n + 1))).card

lemma sum_cons {m : ℕ} (f : (Fin (m + 1) → Fin 7) → ℕ) :
    ∑ x, f x = ∑ c : Fin 7, ∑ y : Fin m → Fin 7, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Fin 7)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma card_ne (v : Fin 7) :
    (Finset.univ.filter (fun c : Fin 7 => c ≠ v)).card = 6 := by
  fin_cases v <;> decide +kernel

lemma card_lt (r : Fin 7) :
    (Finset.univ.filter (fun v : Fin 7 => v.val ≤ r.val)).card = r.val + 1 := by
  fin_cases r <;> decide +kernel

lemma sum_bound (m : ℕ) :
    ∑ r : Fin 7, (r.val + 1) ^ m = 1 ^ m + 2 ^ m + 3 ^ m + 4 ^ m + 5 ^ m + 6 ^ m + 7 ^ m := by
  simp [Fin.sum_univ_succ]; ring

lemma a_step (m : ℕ) :
    a (m + 2) = 6 * a (m + 1) + (1 ^ m + 2 ^ m + 3 ^ m + 4 ^ m + 5 ^ m + 6 ^ m + 7 ^ m) := by
  simp only [a, Finset.card_filter]
  rw [sum_cons]
  have hsplit : ∀ (c : Fin 7) (y : Fin (m + 1) → Fin 7),
      (if isValid (Fin.cons c y) then (1 : ℕ) else 0) =
      (if c = y 0 then (if ∀ j : Fin m, (y j.succ).val ≤ c.val then 1 else 0) else 0) +
      (if c ≠ y 0 then (if isValid y then 1 else 0) else 0) := by
    intro c y
    have hv : isValid (Fin.cons c y) ↔
        if c = y 0 then ∀ j : Fin m, (y j.succ).val ≤ c.val else isValid y := by
      simp [isValid]
    by_cases h : c = y 0
    · rw [if_pos h] at hv
      rw [if_pos h, if_neg (not_not.mpr h), add_zero]
      simp only [hv]
    · rw [if_neg h] at hv
      rw [if_neg h, if_pos h, zero_add]
      simp only [hv]
  simp only [hsplit, Finset.sum_add_distrib]
  have h1 : ∑ c : Fin 7, ∑ y : Fin (m + 1) → Fin 7,
      (if c = y 0 then (if ∀ j : Fin m, (y j.succ).val ≤ c.val then (1 : ℕ) else 0) else 0) =
      1 ^ m + 2 ^ m + 3 ^ m + 4 ^ m + 5 ^ m + 6 ^ m + 7 ^ m := by
    rw [← sum_bound m]
    apply Finset.sum_congr rfl
    intro r _
    rw [sum_cons]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [Finset.sum_eq_single r]
    · simp only [↓reduceIte]
      have hcard : ∑ z : Fin m → Fin 7, (if ∀ j : Fin m, (z j).val ≤ r.val then (1 : ℕ) else 0) =
          (Fintype.piFinset (fun _ : Fin m => Finset.univ.filter (fun v : Fin 7 => v.val ≤ r.val))).card := by
        rw [← Finset.card_filter]
        congr 1; ext z
        simp [Fintype.mem_piFinset]
      simp only [hcard, Fintype.card_piFinset_const, card_lt r, Fintype.card_fin]
    · intro b _ hb
      apply Finset.sum_eq_zero; intro z _
      simp [Ne.symm hb]
    · simp
  have h2 : ∑ c : Fin 7, ∑ y : Fin (m + 1) → Fin 7,
      (if c ≠ y 0 then (if isValid y then (1 : ℕ) else 0) else 0) =
      6 * ∑ y : Fin (m + 1) → Fin 7, if isValid y then 1 else 0 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : isValid y
    · simp only [hy, ↓reduceIte, mul_one]
      rw [← Finset.card_filter, card_ne (y 0)]
    · simp [hy]
  rw [h1, h2, add_comm]

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 7 := by
  decide +kernel

def cf (n : ℕ) : ℚ :=
  (-504 - 315 * (2 : ℚ) ^ n - 280 * (3 : ℚ) ^ n - 315 * (4 : ℚ) ^ n - 504 * (5 : ℚ) ^ n + 3409 * (6 : ℚ) ^ n + 360 * (7 : ℚ) ^ n + 35 * (2 : ℚ) ^ (1 + n) * (3 : ℚ) ^ n * n) / 2520

theorem main_proof_ours :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 34 * a (n - 1) - 490 * a (n - 2) + 3892 * a (n - 3) - 18529 * a (n - 4) + 53746 * a (n - 5) - 91860 * a (n - 6) + 83448 * a (n - 7) - 30240 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2 * (1 - 7 * X)) =
      X * (7 - 189 * X + 2086 * X ^ 2 - 12110 * X ^ 3 + 39543 * X ^ 4 - 71617 * X ^ 5 + 65212 * X ^ 6 - 22212 * X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-504 - 315 * (2 : ℚ) ^ n - 280 * (3 : ℚ) ^ n - 315 * (4 : ℚ) ^ n - 504 * (5 : ℚ) ^ n + 3409 * (6 : ℚ) ^ n + 360 * (7 : ℚ) ^ n + 35 * (2 : ℚ) ^ (1 + n) * (3 : ℚ) ^ n * n) / 2520) := by
  have h4 : ∀ k : ℕ, (4 : ℚ) ^ k = ((2 : ℚ) ^ k) ^ 2 := fun k => by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h6 : ∀ k : ℕ, (6 : ℚ) ^ k = (2 : ℚ) ^ k * (3 : ℚ) ^ k := fun k => by rw [← mul_pow]; norm_num
  have h8 : ∀ k : ℕ, (8 : ℚ) ^ k = ((2 : ℚ) ^ k) ^ 3 := fun k => by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h22 : ∀ k : ℕ, (2 : ℚ) ^ (2 * k) = ((2 : ℚ) ^ k) ^ 2 := fun k => by rw [← pow_mul, mul_comm, pow_mul]
  have hcf_step : ∀ m : ℕ, cf (m + 2) = 6 * cf (m + 1) + ((1 : ℚ) ^ (m) + (2 : ℚ) ^ (m) + (3 : ℚ) ^ (m) + (4 : ℚ) ^ (m) + (5 : ℚ) ^ (m) + (6 : ℚ) ^ (m) + (7 : ℚ) ^ (m)) := by
    intro m
    unfold cf
    simp only [one_pow, h4, h6, h8, pow_add, pow_mul, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]; ring
  have hcf : (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-504 - 315 * (2 : ℚ) ^ n - 280 * (3 : ℚ) ^ n - 315 * (4 : ℚ) ^ n - 504 * (5 : ℚ) ^ n + 3409 * (6 : ℚ) ^ n + 360 * (7 : ℚ) ^ n + 35 * (2 : ℚ) ^ (1 + n) * (3 : ℚ) ^ n * n) / 2520) := by
    have haux : ∀ m : ℕ, (a (m + 1) : ℚ) = cf (m + 1) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add, a_1, cf]
        norm_num [zpow_sub₀, zpow_natCast]
      | succ m ih =>
        have hs : (a (m + 1 + 1) : ℚ) = 6 * (a (m + 1) : ℚ) + ((1 : ℚ) ^ (m) + (2 : ℚ) ^ (m) + (3 : ℚ) ^ (m) + (4 : ℚ) ^ (m) + (5 : ℚ) ^ (m) + (6 : ℚ) ^ (m) + (7 : ℚ) ^ (m)) := by
          have h0 := a_step (m)
          rw [show m + 2 = m + 1 + 1 by omega, show m + 1 = m + 1 by omega] at h0
          exact_mod_cast h0
        rw [hs, ih, show m + 1 + 1 = m + 2 by omega]
        exact (hcf_step m).symm
    intro n hn
    have h := haux (n - 1)
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  have hrec : (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 34 * a (n - 1) - 490 * a (n - 2) + 3892 * a (n - 3) - 18529 * a (n - 4) + 53746 * a (n - 5) - 91860 * a (n - 6) + 83448 * a (n - 7) - 30240 * a (n - 8)) := by
    intro n hn
    have hq : (a n : ℚ) = 34 * a (n - 1) - 490 * a (n - 2) + 3892 * a (n - 3) - 18529 * a (n - 4) + 53746 * a (n - 5) - 91860 * a (n - 6) + 83448 * a (n - 7) - 30240 * a (n - 8) := by
      have ha0 : (a n : ℚ) = cf n := hcf n (by omega)
      have ha : ∀ j : ℕ, j ≤ 8 → (a (n - j) : ℚ) = cf (n - j) := fun j hj => hcf (n - j) (by omega)
      simp only [ha0, ha 1 (by omega), ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega), ha 6 (by omega), ha 7 (by omega), ha 8 (by omega)]
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega]
      unfold cf
      simp only [one_pow, h4, h6, h8, pow_add, pow_mul, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]; ring
    exact_mod_cast hq
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2 * (1 - 7 * X)) =
      X * (7 - 189 * X + 2086 * X ^ 2 - 12110 * X ^ 3 + 39543 * X ^ 4 - 71617 * X ^ 5 + 65212 * X ^ 6 - 22212 * X ^ 7)) := by
    have hden : ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2 * (1 - 7 * X) : PowerSeries ℚ) = 1 - 34 * X + 490 * X ^ 2 - 3892 * X ^ 3 + 18529 * X ^ 4 - 53746 * X ^ 5 + 91860 * X ^ 6 - 83448 * X ^ 7 + 30240 * X ^ 8 := by
      have p1 : ((1 - X) * (1 - 2 * X) : PowerSeries ℚ) = 1 - 3 * X + 2 * X ^ 2 := by ring
      have p2 : ((1 - 3 * X + 2 * X ^ 2) * (1 - 3 * X) : PowerSeries ℚ) = 1 - 6 * X + 11 * X ^ 2 - 6 * X ^ 3 := by ring
      have p3 : ((1 - 6 * X + 11 * X ^ 2 - 6 * X ^ 3) * (1 - 4 * X) : PowerSeries ℚ) = 1 - 10 * X + 35 * X ^ 2 - 50 * X ^ 3 + 24 * X ^ 4 := by ring
      have p4 : ((1 - 10 * X + 35 * X ^ 2 - 50 * X ^ 3 + 24 * X ^ 4) * (1 - 5 * X) : PowerSeries ℚ) = 1 - 15 * X + 85 * X ^ 2 - 225 * X ^ 3 + 274 * X ^ 4 - 120 * X ^ 5 := by ring
      have p5 : ((1 - 15 * X + 85 * X ^ 2 - 225 * X ^ 3 + 274 * X ^ 4 - 120 * X ^ 5) * (1 - 6 * X) ^ 2 : PowerSeries ℚ) = 1 - 27 * X + 301 * X ^ 2 - 1785 * X ^ 3 + 6034 * X ^ 4 - 11508 * X ^ 5 + 11304 * X ^ 6 - 4320 * X ^ 7 := by ring
      have p6 : ((1 - 27 * X + 301 * X ^ 2 - 1785 * X ^ 3 + 6034 * X ^ 4 - 11508 * X ^ 5 + 11304 * X ^ 6 - 4320 * X ^ 7) * (1 - 7 * X) : PowerSeries ℚ) = 1 - 34 * X + 490 * X ^ 2 - 3892 * X ^ 3 + 18529 * X ^ 4 - 53746 * X ^ 5 + 91860 * X ^ 6 - 83448 * X ^ 7 + 30240 * X ^ 8 := by ring
      rw [p1, p2, p3, p4, p5, p6]
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X) * (1 - 5 * X) * (1 - 6 * X) ^ 2 * (1 - 7 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (34 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (490 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (3892 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (18529 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (53746 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        + C (91860 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        - C (83448 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7)
        + C (30240 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 8) := by
      rw [hden]
      simp only [map_ofNat]; ring
    have hr : (X * (7 - 189 * X + 2086 * X ^ 2 - 12110 * X ^ 3 + 39543 * X ^ 4 - 71617 * X ^ 5 + 65212 * X ^ 6 - 22212 * X ^ 7) : PowerSeries ℚ) =
        C (7 : ℚ) * X ^ 1
        - C (189 : ℚ) * X ^ 2
        + C (2086 : ℚ) * X ^ 3
        - C (12110 : ℚ) * X ^ 4
        + C (39543 : ℚ) * X ^ 5
        - C (71617 : ℚ) * X ^ 6
        + C (65212 : ℚ) * X ^ 7
        - C (22212 : ℚ) * X ^ 8 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have hv_0 : (a 0 : ℚ) = 0 := by exact_mod_cast a_0
    have hv_1 : (a 1 : ℚ) = 7 := by exact_mod_cast a_1
    have hv_2 : (a 2 : ℚ) = 49 := by rw [hcf 2 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    have hv_3 : (a 3 : ℚ) = 322 := by rw [hcf 3 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    have hv_4 : (a 4 : ℚ) = 2072 := by rw [hcf 4 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    have hv_5 : (a 5 : ℚ) = 13216 := by rw [hcf 5 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    have hv_6 : (a 6 : ℚ) = 83972 := by rw [hcf 6 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    have hv_7 : (a 7 : ℚ) = 532840 := by rw [hcf 7 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    have hv_8 : (a 8 : ℚ) = 3381860 := by rw [hcf 8 (by omega)]; norm_num [zpow_sub₀, zpow_natCast]
    rcases Nat.lt_or_ge n 9 with hn | hn
    · interval_cases n <;> norm_num [coeff_C, hv_0, hv_1, hv_2, hv_3, hv_4, hv_5, hv_6, hv_7, hv_8]
    · have hq : (a n : ℚ) = 34 * a (n - 1) - 490 * a (n - 2) + 3892 * a (n - 3) - 18529 * a (n - 4) + 53746 * a (n - 5) - 91860 * a (n - 6) + 83448 * a (n - 7) - 30240 * a (n - 8) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have c5 : 5 ≤ n := by omega
      have c6 : 6 ≤ n := by omega
      have c7 : 7 ≤ n := by omega
      have c8 : 8 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      have e6 : n - 6 ≠ 0 := by omega
      have e7 : n - 7 ≠ 0 := by omega
      have e8 : n - 8 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, c5, c6, c7, c8, e1, e2, e3, e4, e5, e6, e7, e8, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  exact ⟨hrec, hgf, hcf⟩


lemma valid_iff : ∀ (n : ℕ) (x : Fin n → Fin 7),
    OMA.S_oeis_a267469.ok (List.ofFn (fun i => ((x i : Fin 7) : ℕ))) = true ↔ isValid x
  | 0, x => by simp [OMA.S_oeis_a267469.ok, isValid]
  | 1, x => by simp [List.ofFn_succ, OMA.S_oeis_a267469.ok, isValid]
  | n + 2, x => by
    have ih := valid_iff (n + 1) (fun i => x i.succ)
    rw [List.ofFn_succ] at ih
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [OMA.S_oeis_a267469.ok]
    unfold isValid
    by_cases h : x 0 = x 1
    · have h' : ((x 0 : Fin 7) : ℕ) = ((x 1 : Fin 7) : ℕ) := by rw [h]
      simp only [Fin.succ_zero_eq_one, h', if_true, h]
      simp [List.all_eq_true, List.mem_ofFn]
    · have h' : ((x 0 : Fin 7) : ℕ) ≠ ((x 1 : Fin 7) : ℕ) := fun e => h (Fin.ext e)
      simp only [Fin.succ_zero_eq_one, h', if_false, h]
      exact ih

lemma a_eq (m : ℕ) : OMA.S_oeis_a267469.a (m + 1) = a (m + 1) := by
  unfold OMA.S_oeis_a267469.a
  show _ = (Finset.univ.filter (isValid (n := m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact valid_iff (m + 1) x

theorem main_proof : type_of% @OMA.S_oeis_a267469.main := by
  obtain ⟨_, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.X * PowerSeries.mk (fun n => (OMA.S_oeis_a267469.a (n + 1) : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => rw [PowerSeries.coeff_succ_X_mul]; simp [a_eq]
  refine ⟨by rw [hser]; exact hgf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_eq m]
  exact hcf (m + 1) hn

end OMA.P267469

theorem OMA.solution : type_of% @OMA.S_oeis_a267469.main := OMA.P267469.main_proof
