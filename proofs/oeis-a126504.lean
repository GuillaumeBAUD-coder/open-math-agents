import OMAStatements.S_oeis_a126504

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix over first digit; the adjacency operator annihilates the recurrence polynomial on the all-ones vector.

namespace OMA.P126504

open OMA.S_oeis_a126504 PowerSeries

abbrev Digit := Fin 9

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

def vtab1 : Digit → ℕ := ( ![5, 6, 7, 8, 9, 8, 7, 6, 5] : Fin 9 → ℕ)
def vtab2 : Digit → ℕ := ( ![35, 43, 50, 56, 61, 56, 50, 43, 35] : Fin 9 → ℕ)
def vtab3 : Digit → ℕ := ( ![245, 301, 351, 394, 429, 394, 351, 301, 245] : Fin 9 → ℕ)
def vtab4 : Digit → ℕ := ( ![1720, 2114, 2465, 2766, 3011, 2766, 2465, 2114, 1720] : Fin 9 → ℕ)
def vtab5 : Digit → ℕ := ( ![12076, 14842, 17307, 19421, 21141, 19421, 17307, 14842, 12076] : Fin 9 → ℕ)

lemma v_0 : ∀ r : Digit, v 0 r = 1 := fun _ => rfl
lemma v_1 : ∀ r : Digit, v 1 r = vtab1 r := by decide
lemma v_2 : ∀ r : Digit, v 2 r = vtab2 r := by
  intro r; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1]; revert r; decide
lemma v_3 : ∀ r : Digit, v 3 r = vtab3 r := by
  intro r; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2]; revert r; decide
lemma v_4 : ∀ r : Digit, v 4 r = vtab4 r := by
  intro r; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3]; revert r; decide
lemma v_5 : ∀ r : Digit, v 5 r = vtab5 r := by
  intro r; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4]; revert r; decide

def err (m : ℕ) (r : Digit) : ℤ :=
  (v (m + 5) r : ℤ) - 7 * (v (m + 4) r : ℤ) - (v (m + 3) r : ℤ) + 6 * (v (m + 2) r : ℤ) - (v m r : ℤ)

lemma err_zero : ∀ r : Digit, err 0 r = 0 := by
  intro r
  change (v 5 r : ℤ) - 7 * (v 4 r : ℤ) - (v 3 r : ℤ) + 6 * (v 2 r : ℤ) - (v 0 r : ℤ) = 0
  simp only [v_5, v_4, v_3, v_2, v_1, v_0]
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
    (a (m + 6) : ℤ) = 7 * a (m + 5) + a (m + 4) - 6 * a (m + 3) + a (m + 1) := by
  have h : ∑ r : Digit, err m r = 0 := Finset.sum_eq_zero (fun r _ => err_eq_zero m r)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [a_succ, Nat.cast_sum]
  linarith

lemma a_1 : a 1 = 9 := by rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]; decide
lemma a_2 : a 2 = 61 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 1 r = 61
  simp only [v_1]; decide
lemma a_3 : a 3 = 429 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 2 r = 429
  simp only [v_2]; decide
lemma a_4 : a 4 = 3011 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 3 r = 3011
  simp only [v_3]; decide
lemma a_5 : a 5 = 21141 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 4 r = 21141
  simp only [v_4]; decide
lemma a_6 : a 6 = 148433 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ r : Digit, v 5 r = 148433
  simp only [v_5]; decide

theorem main_proof :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X - X ^ 2 + 6 * X ^ 3 - X ^ 5) =
      (1 - X) * (1 + 3 * X - X ^ 3)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 7 * a (n - 1) + a (n - 2) - 6 * a (n - 3) + a (n - 5)) := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 7 * a (n - 1) + a (n - 2) - 6 * a (n - 3) + a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simpa using a_rec_ge m
  refine ⟨?_, hrec⟩
  have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X - X ^ 2 + 6 * X ^ 3 - X ^ 5) =
      PowerSeries.mk (fun n => (a n : ℚ))
        - C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) := by
    simp only [map_ofNat, map_one]; ring
  have hr : ((1 - X) * (1 + 3 * X - X ^ 3) : PowerSeries ℚ) =
      C (1 : ℚ) + C (2 : ℚ) * X ^ 1 - C (3 : ℚ) * X ^ 2 - C (1 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
    simp only [map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp [a_zero, a_1, a_2, a_3, a_4, a_5] <;> try norm_num
  · have hq : (a n : ℚ) = 7 * a (n - 1) + a (n - 2) - 6 * a (n - 3) + a (n - 5) := by
      exact_mod_cast hrec n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have e0 : n ≠ 0 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, c5, e0, e1, e2, e3, e4, coeff_C, if_true, if_false]
    rw [hq]; ring

end OMA.P126504

theorem OMA.solution : type_of% @OMA.S_oeis_a126504.main := OMA.P126504.main_proof
