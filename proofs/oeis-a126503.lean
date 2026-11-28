import OMAStatements.S_oeis_a126503

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix over first digit; the adjacency operator annihilates the recurrence polynomial on the all-ones vector.

namespace OMA.P126503

open OMA.S_oeis_a126503 PowerSeries

abbrev Digit := Fin 8

def step (f : Digit → ℕ) (r : Digit) : ℕ :=
  ∑ s : Digit, if adjOk r s then f s else 0

def v : ℕ → Digit → ℕ
  | 0, _ => 1
  | m + 1, r => step (v m) r

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

lemma isValid_cons (m : ℕ) (r : Digit) (y : Fin (m + 1) → Digit) :
    isValid (m + 2) (Fin.cons r y) ↔ adjOk r (y 0) ∧ isValid (m + 1) y := by
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

def N (m : ℕ) (r : Digit) : ℕ :=
  ∑ w : Fin (m + 1) → Digit, if w 0 = r ∧ isValid (m + 1) w then 1 else 0

lemma N_zero (r : Digit) : N 0 r = 1 := by
  unfold N
  have hv : ∀ w : Fin 1 → Digit, isValid 1 w := fun _ i => Fin.elim0 i
  simp only [hv, and_true]
  rw [← (Equiv.funUnique (Fin 1) Digit).symm.sum_comp]
  simp

lemma N_succ (m : ℕ) (r : Digit) : N (m + 1) r = step (N m) r := by
  unfold N step
  rw [sum_cons]
  simp only [Fin.cons_zero]
  rw [Finset.sum_eq_single r (by intro b _ hb; simp [hb]) (by simp)]
  simp only [true_and, isValid_cons]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : adjOk r s
  · rw [if_pos hs]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = s <;> simp [hy, hs]
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y 0 = s <;> simp [hy, hs]

lemma N_eq_v (m : ℕ) (r : Digit) : N m r = v m r := by
  induction m generalizing r with
  | zero => exact N_zero r
  | succ m ih =>
    rw [N_succ, v]
    unfold step
    apply Finset.sum_congr rfl
    intro s _
    rw [ih s]

lemma a_zero : a 0 = 1 := by
  unfold a
  rw [Finset.card_filter]
  have hv : ∀ w : Fin 0 → Digit, isValid 0 w := fun _ i => Fin.elim0 i
  simp [hv]

lemma a_succ (m : ℕ) : a (m + 1) = ∑ r : Digit, v m r := by
  unfold a
  rw [Finset.card_filter, fiber]
  apply Finset.sum_congr rfl
  intro r _
  rw [← N_eq_v]
  unfold N
  apply Finset.sum_congr rfl
  intro y _
  rw [ite_and]

def vtab1 : Digit → ℕ := ( ![5, 6, 7, 8, 8, 7, 6, 5] : Fin 8 → ℕ)
def vtab2 : Digit → ℕ := ( ![34, 41, 47, 52, 52, 47, 41, 34] : Fin 8 → ℕ)
def vtab3 : Digit → ℕ := ( ![226, 273, 314, 348, 348, 314, 273, 226] : Fin 8 → ℕ)
def vtab4 : Digit → ℕ := ( ![1509, 1823, 2096, 2322, 2322, 2096, 1823, 1509] : Fin 8 → ℕ)

lemma v_0 : ∀ r : Digit, v 0 r = 1 := fun _ => rfl
lemma v_1 : ∀ r : Digit, v 1 r = vtab1 r := by decide
lemma v_2 : ∀ r : Digit, v 2 r = vtab2 r := by
  intro r; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1]; revert r; decide
lemma v_3 : ∀ r : Digit, v 3 r = vtab3 r := by
  intro r; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2]; revert r; decide
lemma v_4 : ∀ r : Digit, v 4 r = vtab4 r := by
  intro r; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3]; revert r; decide

def err (m : ℕ) (r : Digit) : ℤ :=
  (v (m + 4) r : ℤ) - 6 * (v (m + 3) r : ℤ) - 5 * (v (m + 2) r : ℤ) + 3 * (v (m + 1) r : ℤ) + 2 * (v m r : ℤ)

lemma err_zero : ∀ r : Digit, err 0 r = 0 := by
  intro r
  change (v 4 r : ℤ) - 6 * (v 3 r : ℤ) - 5 * (v 2 r : ℤ) + 3 * (v 1 r : ℤ) + 2 * (v 0 r : ℤ) = 0
  rw [v_4, v_3, v_2, v_1, v_0]
  revert r; decide

lemma err_succ (m : ℕ) (r : Digit) :
    err (m + 1) r = ∑ s : Digit, if adjOk r s then err m s else 0 := by
  have hV : ∀ j, (v (j + 1) r : ℤ) = ∑ s : Digit, if adjOk r s then (v j s : ℤ) else 0 := by
    intro j; rw [v, step]; simp
  unfold err
  simp only [Nat.add_right_comm, hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> ring

lemma err_eq_zero (m : ℕ) (r : Digit) : err m r = 0 := by
  induction m generalizing r with
  | zero => exact err_zero r
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun s _ => by simp [ih s])

lemma a_rec_ge (m : ℕ) :
    (a (m + 5) : ℤ) = 6 * a (m + 4) + 5 * a (m + 3) - 3 * a (m + 2) - 2 * a (m + 1) := by
  have h : ∑ r : Digit, err m r = 0 := Finset.sum_eq_zero (fun r _ => err_eq_zero m r)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [a_succ, Nat.cast_sum]
  linarith

lemma a_1 : a 1 = 8 := by rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]; decide
lemma a_2 : a 2 = 52 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 1 r = 52
  simp only [v_1]; decide
lemma a_3 : a 3 = 348 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 2 r = 348
  simp only [v_2]; decide
lemma a_4 : a 4 = 2322 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 3 r = 2322
  simp only [v_3]; decide

theorem main_proof :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4) =
      1 + 2 * X - X ^ 2 - X ^ 3) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) + 5 * a (n - 2) - 3 * a (n - 3) - 2 * a (n - 4)) := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) + 5 * a (n - 2) - 3 * a (n - 3) - 2 * a (n - 4) := by
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp [a_zero, a_1, a_2, a_3, a_4]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      simpa using a_rec_ge m
  refine ⟨?_, hrec⟩
  have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 6 * X - 5 * X ^ 2 + 3 * X ^ 3 + 2 * X ^ 4) =
      PowerSeries.mk (fun n => (a n : ℚ))
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by
    simp only [map_ofNat, map_one]; ring
  have hr : (1 + 2 * X - X ^ 2 - X ^ 3 : PowerSeries ℚ) =
      C (1 : ℚ) + C (2 : ℚ) * X ^ 1 - C (1 : ℚ) * X ^ 2 - C (1 : ℚ) * X ^ 3 := by
    simp only [map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [a_zero, a_1, a_2, a_3] <;> try norm_num
  · have hq : (a n : ℚ) = 6 * a (n - 1) + 5 * a (n - 2) - 3 * a (n - 3) - 2 * a (n - 4) := by
      exact_mod_cast hrec n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have e0 : n ≠ 0 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, e0, e1, e2, e3, coeff_C, if_true, if_false]
    rw [hq]; ring

end OMA.P126503

theorem OMA.solution : type_of% @OMA.S_oeis_a126503.main := OMA.P126503.main_proof
