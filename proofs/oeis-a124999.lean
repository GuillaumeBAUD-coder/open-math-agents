import OMAStatements.S_oeis_a124999

-- Credit: @Dariusthedoggie
-- Proof: circular walk count equals trace of transfer matrix powers; the matrix satisfies the degree-3 recurrence from step 1, yielding the recurrence, closed form, and generating function.

namespace OMA.P124999

open OMA.S_oeis_a124999 PowerSeries

abbrev Digit := Fin 5

def isLinValid (n : ℕ) (w : Fin n → Digit) : Prop :=
  ∀ i : Fin (n - 1), adjOk (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)

instance (n : ℕ) (w : Fin n → Digit) : Decidable (isLinValid n w) :=
  inferInstanceAs (Decidable (∀ _, _))

def W : ℕ → Digit → Digit → ℕ
  | 0, s, t => if s = t then 1 else 0
  | m + 1, s, t => ∑ u : Digit, if adjOk s u then W m u t else 0

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Digit) → ℕ) :
    ∑ w, f w = ∑ r : Digit, ∑ y : Fin (m + 1) → Digit, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Digit)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Digit) → ℕ) :
    ∑ y, g y = ∑ s : Digit, ∑ y : Fin (m + 1) → Digit, if y 0 = s then g y else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

lemma fiber_ends (m : ℕ) (g : (Fin (m + 1) → Digit) → ℕ) :
    ∑ y, g y = ∑ t : Digit, ∑ s : Digit,
      ∑ y : Fin (m + 1) → Digit, if y 0 = s ∧ y (Fin.last m) = t then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Digit,
      ∑ t : Digit, ∑ s : Digit, if y 0 = s ∧ y (Fin.last m) = t then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (y (Fin.last m))]
    · rw [Finset.sum_eq_single (y 0)]
      · simp
      · intro s _ hs; simp [Ne.symm hs]
      · simp
    · intro t _ ht
      apply Finset.sum_eq_zero
      intro s _
      simp [Ne.symm ht]
    · simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_comm]

lemma isLinValid_cons (m : ℕ) (r : Digit) (y : Fin (m + 1) → Digit) :
    isLinValid (m + 2) (Fin.cons r y) ↔ adjOk r (y 0) ∧ isLinValid (m + 1) y := by
  have hcs : ∀ (k : ℕ) (hk : k + 1 < m + 2),
      (Fin.cons r y : Fin (m + 2) → Digit) ⟨k + 1, hk⟩ = y ⟨k, by omega⟩ :=
    fun k hk => Fin.cons_succ (α := fun _ => Digit) r y ⟨k, by omega⟩
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h ⟨0, by omega⟩
      simpa [hcs] using h0
    · intro j
      have hj := h ⟨j.val + 1, by omega⟩
      rw [hcs, hcs] at hj
      exact hj
  · rintro ⟨h0, hy⟩ i
    rcases i with ⟨k, hk⟩
    cases k with
    | zero => simpa [hcs] using h0
    | succ k' =>
      rw [hcs, hcs]
      exact hy ⟨k', by omega⟩

lemma isValid_iff (m : ℕ) (w : Fin (m + 1) → Digit) :
    isValid (m + 1) w ↔ isLinValid (m + 1) w ∧ adjOk (w (Fin.last m)) (w 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      have hi := h ⟨i.val, by omega⟩
      have hmod : (i.val + 1) % (m + 1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      simpa [hmod] using hi
    · have hm := h (Fin.last m)
      have hmod : (m + 1) % (m + 1) = 0 := Nat.mod_self (m + 1)
      simpa [Fin.last, hmod] using hm
  · rintro ⟨hlin, hwrap⟩ i
    by_cases hi : i.val < m
    · have hmod : (i.val + 1) % (m + 1) = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      have := hlin ⟨i.val, by omega⟩
      simpa [hmod] using this
    · have him : i.val = m := by omega
      have hi_eq : i = Fin.last m := Fin.ext him
      subst hi_eq
      have hmod : (m + 1) % (m + 1) = 0 := Nat.mod_self (m + 1)
      simpa [Fin.last, hmod] using hwrap

def P (m : ℕ) (s t : Digit) : ℕ :=
  ∑ w : Fin (m + 1) → Digit,
    if w 0 = s ∧ w (Fin.last m) = t ∧ isLinValid (m + 1) w then 1 else 0

lemma P_zero (s t : Digit) : P 0 s t = if s = t then 1 else 0 := by
  unfold P
  have hv : ∀ w : Fin 1 → Digit, isLinValid 1 w := fun _ i => Fin.elim0 i
  simp only [hv, and_true]
  rw [← (Equiv.funUnique (Fin 1) Digit).symm.sum_comp]
  by_cases hst : s = t
  · subst hst
    simp [Fin.last]
  · rw [if_neg hst]
    apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    simp only [Equiv.funUnique_symm_apply, Fin.last]
    intro ⟨h1, h2⟩
    exact hst (h1.symm.trans h2)

lemma P_succ (m : ℕ) (s t : Digit) :
    P (m + 1) s t = ∑ u : Digit, if adjOk s u then P m u t else 0 := by
  unfold P
  rw [sum_cons]
  simp only [Fin.cons_zero]
  rw [Finset.sum_eq_single s (by intro b _ hb; simp [hb]) (by simp)]
  simp only [true_and, isLinValid_cons]
  have hlast : ∀ y : Fin (m + 1) → Digit,
      (Fin.cons s y : Fin (m + 2) → Digit) (Fin.last (m + 1)) = y (Fin.last m) := by
    intro y
    exact Fin.cons_succ (α := fun _ => Digit) s y (Fin.last m)
  simp only [hlast]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : adjOk s u
  · rw [if_pos hu]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = u <;> simp [hy, hu]
  · rw [if_neg hu]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y 0 = u <;> simp [hy, hu]

lemma P_eq_W (m : ℕ) (s t : Digit) : P m s t = W m s t := by
  induction m generalizing s with
  | zero => exact P_zero s t
  | succ m ih =>
    rw [P_succ, W]
    apply Finset.sum_congr rfl
    intro u _
    rw [ih u]

lemma a_zero : a 0 = 1 := by
  unfold a
  rw [Finset.card_filter]
  have hv : ∀ w : Fin 0 → Digit, isValid 0 w := fun _ i => Fin.elim0 i
  simp [hv]

lemma a_succ (m : ℕ) : a (m + 1) = ∑ t : Digit, W (m + 1) t t := by
  unfold a
  rw [Finset.card_filter, fiber_ends]
  apply Finset.sum_congr rfl
  intro t _
  rw [W]
  apply Finset.sum_congr rfl
  intro s _
  rw [← P_eq_W]
  unfold P
  by_cases hts : adjOk t s
  · rw [if_pos hts]
    apply Finset.sum_congr rfl
    intro y _
    by_cases h1 : y 0 = s <;> by_cases h2 : y (Fin.last m) = t <;> simp [h1, h2, isValid_iff, hts]
  · rw [if_neg hts]
    apply Finset.sum_eq_zero
    intro y _
    by_cases h1 : y 0 = s <;> by_cases h2 : y (Fin.last m) = t <;> simp [h1, h2, isValid_iff, hts]

def err (m : ℕ) (s t : Digit) : ℤ :=
  (W (m + 3) s t : ℤ) - 5 * (W (m + 2) s t : ℤ) + (W (m + 1) s t : ℤ) + 3 * (W m s t : ℤ)

lemma err_one : ∀ s t : Digit, err 1 s t = 0 := by decide

lemma err_succ (m : ℕ) (s t : Digit) :
    err (m + 1) s t = ∑ u : Digit, if adjOk s u then err m u t else 0 := by
  unfold err
  simp only [W, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> ring

lemma err_pos_zero (m : ℕ) (s t : Digit) : err (m + 1) s t = 0 := by
  induction m generalizing s with
  | zero => exact err_one s t
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun u _ => by simp [ih u])

lemma a_rec_ge4 (m : ℕ) :
    (a (m + 4) : ℤ) = 5 * a (m + 3) - a (m + 2) - 3 * a (m + 1) := by
  have h : ∑ s : Digit, err (m + 1) s s = 0 :=
    Finset.sum_eq_zero (fun s _ => err_pos_zero m s s)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [a_succ, Nat.cast_sum]
  linarith

lemma a_1 : a 1 = 5 := by rw [a_succ]; decide
lemma a_2 : a 2 = 23 := by rw [a_succ]; decide
lemma a_3 : a 3 = 101 := by rw [a_succ]; decide

lemma closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = 1 + (2 - Real.sqrt 7) ^ n + (2 + Real.sqrt 7) ^ n := by
  have hsq : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n
      · rw [a_1]; push_cast; ring
      · rw [a_2]; push_cast; ring_nf; rw [hsq]; norm_num
      · rw [a_3]; push_cast; ring_nf; rw [hsq]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hrec : (a (m + 4) : ℝ) = 5 * a (m + 3) - a (m + 2) - 3 * a (m + 1) := by
        exact_mod_cast a_rec_ge4 m
      rw [hrec, ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega),
        ih (m + 1) (by omega) (by omega)]
      set r1 : ℝ := 2 - Real.sqrt 7
      set r2 : ℝ := 2 + Real.sqrt 7
      have hr1 : r1 ^ 2 - 4 * r1 - 3 = 0 := by dsimp [r1]; ring_nf; rw [hsq]; norm_num
      have hr2 : r2 ^ 2 - 4 * r2 - 3 = 0 := by dsimp [r2]; ring_nf; rw [hsq]; norm_num
      have h1 : r1 ^ (m + 4) = 5 * r1 ^ (m + 3) - r1 ^ (m + 2) - 3 * r1 ^ (m + 1) := by
        linear_combination r1 ^ (m + 1) * (r1 - 1) * hr1
      have h2 : r2 ^ (m + 4) = 5 * r2 ^ (m + 3) - r2 ^ (m + 2) - 3 * r2 ^ (m + 1) := by
        linear_combination r2 ^ (m + 1) * (r2 - 1) * hr2
      linarith

theorem main_proof :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X - 3 * X ^ 2)) =
      (1 - 2 * X) * (1 + 2 * X + 3 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 + (2 - Real.sqrt 7) ^ n + (2 + Real.sqrt 7) ^ n) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 5 * a (n - 1) - a (n - 2) - 3 * a (n - 3)) := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 5 * a (n - 1) - a (n - 2) - 3 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using a_rec_ge4 m
  refine ⟨?_, closed_form, hrec⟩
  have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X - 3 * X ^ 2)) =
      PowerSeries.mk (fun n => (a n : ℚ)) -
        C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) +
        C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) +
        C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
    simp only [map_ofNat, map_one]; ring
  have hr : ((1 : PowerSeries ℚ) - 2 * X) * (1 + 2 * X + 3 * X ^ 2) =
      C (1 : ℚ) - C (1 : ℚ) * X ^ 2 - C (6 : ℚ) * X ^ 3 := by
    simp only [map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [a_zero, a_1, a_2, a_3] <;> norm_num
  · have hq : (a n : ℚ) = 5 * a (n - 1) - a (n - 2) - 3 * a (n - 3) := by
      exact_mod_cast hrec n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have e0 : n ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    simp only [c1, c2, c3, e0, e2, e3, coeff_C, if_true, if_false]
    rw [hq]; ring

end OMA.P124999

theorem OMA.solution : type_of% @OMA.S_oeis_a124999.main := OMA.P124999.main_proof
