import OMAStatements.S_oeis_a207363

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix over rows annihilated by the order-8 recurrence polynomial, giving g.f. and closed forms, bridged to the get/avoids encoding.

namespace OMA.P207363

open PowerSeries
/-- A horizontal row of length 3 avoids `(0, 0, 0)` and `(0, 1, 1)`. -/
def rowOk (r : Fin 3 → Fin 2) : Prop :=
  (r 0, r 1, r 2) ≠ (0, 0, 0) ∧ (r 0, r 1, r 2) ≠ (0, 1, 1)

instance (r : Fin 3 → Fin 2) : Decidable (rowOk r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A vertical triple avoids `(0, 0, 1)` and `(0, 1, 1)`. -/
def colTripOk (a b c : Fin 2) : Prop :=
  (a, b, c) ≠ (0, 0, 1) ∧ (a, b, c) ≠ (0, 1, 1)

instance (a b c : Fin 2) : Decidable (colTripOk a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An `n X 3` binary array avoids the forbidden horizontal and vertical triples. -/
def isValid (n : ℕ) (x : Fin n → Fin 3 → Fin 2) : Prop :=
  (∀ i : Fin n, rowOk (x i)) ∧
  (∀ i : Fin (n - 2), ∀ j : Fin 3,
    colTripOk (x ⟨i.val, by omega⟩ j) (x ⟨i.val + 1, by omega⟩ j) (x ⟨i.val + 2, by omega⟩ j))

instance (n : ℕ) (x : Fin n → Fin 3 → Fin 2) : Decidable (isValid n x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A207363: the number of n X 3 0..1 arrays avoiding 0 0 0 and 0 1 1 horizontally and 0 0 1 and 0 1 1 vertically. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Slice := Fin 3 → Fin 2

def sliceOk (r : Slice) : Prop := rowOk r

instance (r : Slice) : Decidable (sliceOk r) :=
  inferInstanceAs (Decidable (_ ∧ _))

def tripOk (r1 r2 r3 : Slice) : Prop := ∀ c : Fin 3, colTripOk (r1 c) (r2 c) (r3 c)

instance (r1 r2 r3 : Slice) : Decidable (tripOk r1 r2 r3) :=
  inferInstanceAs (Decidable (∀ _, _))

def isValidS (n : ℕ) (x : Fin n → Slice) : Prop :=
  (∀ i : Fin n, sliceOk (x i)) ∧
  (∀ i : Fin (n - 2), tripOk (x ⟨i.val, by omega⟩) (x ⟨i.val + 1, by omega⟩) (x ⟨i.val + 2, by omega⟩))

instance (n : ℕ) (x : Fin n → Slice) : Decidable (isValidS n x) :=
  inferInstanceAs (Decidable (_ ∧ _))

def enc (r : Slice) : Fin 8 :=
  ⟨4 * (r 0).val + 2 * (r 1).val + (r 2).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega⟩

def dec (k : Fin 8) : Slice
  | ⟨0, _⟩ => ⟨k.val / 4, by omega⟩
  | ⟨1, _⟩ => ⟨(k.val / 2) % 2, by omega⟩
  | ⟨2, _⟩ => ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 8, enc (dec k) = k := by decide

lemma dec_enc : ∀ r : Slice, dec (enc r) = r := by decide

def rowEquiv : Slice ≃ Fin 8 where
  toFun := enc
  invFun := dec
  left_inv := dec_enc
  right_inv := enc_dec

def ok1 (i : Fin 8) : Prop := sliceOk (dec i)

instance (i : Fin 8) : Decidable (ok1 i) :=
  inferInstanceAs (Decidable (sliceOk _))

def ok3 (i j k : Fin 8) : Prop := tripOk (dec i) (dec j) (dec k)

instance (i j k : Fin 8) : Decidable (ok3 i j k) :=
  inferInstanceAs (Decidable (tripOk _ _ _))

def step (f : Fin 8 → Fin 8 → ℕ) (i j : Fin 8) : ℕ :=
  if ok1 i then ∑ l : Fin 8, if ok3 i j l then f j l else 0 else 0

def v : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, i, j => if ok1 i ∧ ok1 j then 1 else 0
  | m + 1, i, j => step (v m) i j

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Slice) → ℕ) :
    ∑ x, f x = ∑ r : Slice, ∑ y : Fin (m + 1) → Slice, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Slice)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber2 (m : ℕ) (g : (Fin (m + 2) → Slice) → ℕ) :
    ∑ y, g y = ∑ i : Fin 8, ∑ j : Fin 8,
      ∑ y : Fin (m + 2) → Slice, if enc (y 0) = i ∧ enc (y 1) = j then g y else 0 := by
  trans ∑ y : Fin (m + 2) → Slice,
      ∑ i : Fin 8, ∑ j : Fin 8, if enc (y 0) = i ∧ enc (y 1) = j then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0))]
    · rw [Finset.sum_eq_single (enc (y 1))]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    · intro i _ hi
      apply Finset.sum_eq_zero
      intro j _
      simp [Ne.symm hi]
    · simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]

lemma fiber1 (m : ℕ) (g : (Fin (m + 2) → Slice) → ℕ) :
    ∑ y, g y = ∑ l : Fin 8, ∑ y : Fin (m + 2) → Slice, if enc (y 1) = l then g y else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

lemma isValidS_cons (m : ℕ) (r : Slice) (y : Fin (m + 2) → Slice) :
    isValidS (m + 3) (Fin.cons r y) ↔
      sliceOk r ∧ tripOk r (y 0) (y 1) ∧ isValidS (m + 2) y := by
  have hcs : ∀ (k : ℕ) (hk : k + 1 < m + 3),
      (Fin.cons r y : Fin (m + 3) → Slice) ⟨k + 1, hk⟩ = y ⟨k, by omega⟩ :=
    fun k hk => Fin.cons_succ (α := fun _ => Slice) r y ⟨k, by omega⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h1 0
    · have ht := h2 ⟨0, by omega⟩
      simpa [hcs] using ht
    · intro i
      have hi := h1 ⟨i.val + 1, by omega⟩
      rw [hcs] at hi
      exact hi
    · intro i
      have hi := h2 ⟨i.val + 1, by omega⟩
      rw [hcs, hcs, hcs] at hi
      exact hi
  · rintro ⟨hr, ht, hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · intro i
      rcases i with ⟨k, hk⟩
      cases k with
      | zero => simpa using hr
      | succ k' => rw [hcs]; exact hy1 ⟨k', by omega⟩
    · intro i
      rcases i with ⟨k, hk⟩
      cases k with
      | zero => simpa [hcs] using ht
      | succ k' => rw [hcs, hcs, hcs]; exact hy2 ⟨k', by omega⟩

def N (m : ℕ) (i j : Fin 8) : ℕ :=
  ∑ x : Fin (m + 2) → Slice, if enc (x 0) = i ∧ enc (x 1) = j ∧ isValidS (m + 2) x then 1 else 0

lemma N_zero (i j : Fin 8) : N 0 i j = if ok1 i ∧ ok1 j then 1 else 0 := by
  unfold N
  rw [sum_cons]
  simp only [Fin.cons_zero]
  have h1 : ∀ (r : Slice) (y : Fin 1 → Slice),
      (Fin.cons r y : Fin 2 → Slice) 1 = y 0 :=
    fun r y => Fin.cons_succ (α := fun _ => Slice) r y 0
  simp only [h1]
  rw [Finset.sum_eq_single (dec i)]
  · rw [← (Equiv.funUnique (Fin 1) Slice).symm.sum_comp]
    rw [Finset.sum_eq_single (dec j)]
    · have h0 : ((Equiv.funUnique (Fin 1) Slice).symm (dec j)) 0 = dec j := rfl
      have hv : isValidS (0 + 2) (Fin.cons (dec i) ((Equiv.funUnique (Fin 1) Slice).symm (dec j))) ↔
          ok1 i ∧ ok1 j := by
        unfold isValidS ok1
        constructor
        · rintro ⟨h, _⟩
          exact ⟨by simpa using h 0, by simpa [h1, h0] using h 1⟩
        · rintro ⟨hi, hj⟩
          refine ⟨fun idx => ?_, fun idx => Fin.elim0 idx⟩
          fin_cases idx
          · simpa using hi
          · simpa [h1, h0] using hj
      change (if enc (dec i) = i ∧ enc (((Equiv.funUnique (Fin 1) Slice).symm (dec j)) 0) = j ∧
          isValidS (0 + 2) (Fin.cons (dec i) ((Equiv.funUnique (Fin 1) Slice).symm (dec j))) then 1 else 0) = _
      simp only [h0, enc_dec, true_and, hv]
    · intro s _ hs
      have hne : enc s ≠ j := fun h => hs (by rw [← h, dec_enc])
      simp [enc_dec, hne]
    · simp
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro y _
    have hne : enc r ≠ i := fun h => hr (by rw [← h, dec_enc])
    simp [hne]
  · simp

lemma N_succ (m : ℕ) (i j : Fin 8) : N (m + 1) i j = step (N m) i j := by
  unfold N step
  rw [sum_cons]
  simp only [Fin.cons_zero]
  have h1 : ∀ (r : Slice) (y : Fin (m + 2) → Slice),
      (Fin.cons r y : Fin (m + 3) → Slice) 1 = y 0 :=
    fun r y => Fin.cons_succ (α := fun _ => Slice) r y 0
  simp only [h1]
  rw [Finset.sum_eq_single (dec i)]
  · simp only [enc_dec, true_and, isValidS_cons]
    by_cases hi : ok1 i
    · rw [if_pos hi]
      have hsi : sliceOk (dec i) := hi
      simp only [hsi, true_and]
      rw [fiber1]
      apply Finset.sum_congr rfl
      intro l _
      by_cases h3 : ok3 i j l
      · rw [if_pos h3]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy0 : enc (y 0) = j
        · by_cases hy1 : enc (y 1) = l
          · have hdy0 : y 0 = dec j := by rw [← hy0, dec_enc]
            have hdy1 : y 1 = dec l := by rw [← hy1, dec_enc]
            have ht : tripOk (dec i) (y 0) (y 1) := by rw [hdy0, hdy1]; exact h3
            simp [hy0, hy1, ht]
          · simp [hy0, hy1]
        · simp [hy0]
      · rw [if_neg h3]
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy0 : enc (y 0) = j
        · by_cases hy1 : enc (y 1) = l
          · have hdy0 : y 0 = dec j := by rw [← hy0, dec_enc]
            have hdy1 : y 1 = dec l := by rw [← hy1, dec_enc]
            have ht : ¬ tripOk (dec i) (y 0) (y 1) := by rw [hdy0, hdy1]; exact h3
            simp [hy0, hy1, ht]
          · simp [hy0, hy1]
        · simp [hy0]
    · rw [if_neg hi]
      have hsi : ¬ sliceOk (dec i) := hi
      simp [hsi]
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro y _
    have hne : enc r ≠ i := fun h => hr (by rw [← h, dec_enc])
    simp [hne]
  · simp

lemma N_eq_v (m : ℕ) (i j : Fin 8) : N m i j = v m i j := by
  induction m generalizing i j with
  | zero => exact N_zero i j
  | succ m ih =>
    rw [N_succ, v]
    unfold step
    split_ifs
    · apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> simp [ih]
    · rfl

lemma a_succ_card (n : ℕ) :
    a (n + 1) = ∑ x : Fin (n + 1) → Slice, if isValidS (n + 1) x then 1 else 0 := by
  show (Finset.univ.filter (isValid (n + 1))).card = _
  rw [Finset.card_filter]
  rfl

lemma a_add2 (m : ℕ) : a (m + 2) = ∑ i : Fin 8, ∑ j : Fin 8, v m i j := by
  rw [show m + 2 = (m + 1) + 1 from rfl, a_succ_card, fiber2]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← N_eq_v]
  unfold N
  apply Finset.sum_congr rfl
  intro y _
  by_cases h0 : enc (y 0) = i <;> by_cases h1 : enc (y 1) = j <;> simp [h0, h1]

def vtab0 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 0, 1, 1, 1, 1]] : Fin 8 → Fin 8 → ℕ)
def vtab1 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 1, 1, 1], ![0, 3, 3, 0, 3, 3, 3, 3], ![0, 3, 3, 0, 3, 3, 3, 3], ![0, 6, 6, 0, 6, 6, 6, 6]] : Fin 8 → Fin 8 → ℕ)
def vtab2 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 3, 3, 6], ![0, 1, 1, 0, 1, 3, 3, 6], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 3, 3, 6], ![0, 3, 3, 0, 3, 9, 9, 18], ![0, 3, 3, 0, 3, 9, 9, 18], ![0, 6, 6, 0, 6, 18, 18, 36]] : Fin 8 → Fin 8 → ℕ)
def vtab3 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 3, 3, 6], ![0, 1, 1, 0, 1, 3, 3, 6], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 3, 3, 6], ![0, 5, 5, 0, 5, 15, 15, 30], ![0, 5, 5, 0, 5, 15, 15, 30], ![0, 15, 15, 0, 15, 45, 45, 90]] : Fin 8 → Fin 8 → ℕ)
def vtab4 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 5, 5, 15], ![0, 1, 1, 0, 1, 5, 5, 15], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 5, 5, 15], ![0, 5, 5, 0, 5, 25, 25, 75], ![0, 5, 5, 0, 5, 25, 25, 75], ![0, 15, 15, 0, 15, 75, 75, 225]] : Fin 8 → Fin 8 → ℕ)
def vtab5 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 5, 5, 15], ![0, 1, 1, 0, 1, 5, 5, 15], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 5, 5, 15], ![0, 7, 7, 0, 7, 35, 35, 105], ![0, 7, 7, 0, 7, 35, 35, 105], ![0, 28, 28, 0, 28, 140, 140, 420]] : Fin 8 → Fin 8 → ℕ)
def vtab6 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 7, 7, 28], ![0, 1, 1, 0, 1, 7, 7, 28], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 7, 7, 28], ![0, 7, 7, 0, 7, 49, 49, 196], ![0, 7, 7, 0, 7, 49, 49, 196], ![0, 28, 28, 0, 28, 196, 196, 784]] : Fin 8 → Fin 8 → ℕ)
def vtab7 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 7, 7, 28], ![0, 1, 1, 0, 1, 7, 7, 28], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 7, 7, 28], ![0, 9, 9, 0, 9, 63, 63, 252], ![0, 9, 9, 0, 9, 63, 63, 252], ![0, 45, 45, 0, 45, 315, 315, 1260]] : Fin 8 → Fin 8 → ℕ)
def vtab8 : Fin 8 → Fin 8 → ℕ := (![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 9, 9, 45], ![0, 1, 1, 0, 1, 9, 9, 45], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 1, 0, 1, 9, 9, 45], ![0, 9, 9, 0, 9, 81, 81, 405], ![0, 9, 9, 0, 9, 81, 81, 405], ![0, 45, 45, 0, 45, 405, 405, 2025]] : Fin 8 → Fin 8 → ℕ)

lemma v_0 : ∀ i j : Fin 8, v 0 i j = vtab0 i j := by decide
lemma v_1 : ∀ i j : Fin 8, v 1 i j = vtab1 i j := by
  intro i j; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0]; revert i j; decide
lemma v_2 : ∀ i j : Fin 8, v 2 i j = vtab2 i j := by
  intro i j; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1]; revert i j; decide
lemma v_3 : ∀ i j : Fin 8, v 3 i j = vtab3 i j := by
  intro i j; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2]; revert i j; decide
lemma v_4 : ∀ i j : Fin 8, v 4 i j = vtab4 i j := by
  intro i j; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3]; revert i j; decide
lemma v_5 : ∀ i j : Fin 8, v 5 i j = vtab5 i j := by
  intro i j; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4]; revert i j; decide
lemma v_6 : ∀ i j : Fin 8, v 6 i j = vtab6 i j := by
  intro i j; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5]; revert i j; decide
lemma v_7 : ∀ i j : Fin 8, v 7 i j = vtab7 i j := by
  intro i j; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6]; revert i j; decide
lemma v_8 : ∀ i j : Fin 8, v 8 i j = vtab8 i j := by
  intro i j; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7]; revert i j; decide

def err (m : ℕ) (i j : Fin 8) : ℤ :=
  (v (m + 8) i j : ℤ) - 2 * (v (m + 7) i j : ℤ) - 2 * (v (m + 6) i j : ℤ) + 6 * (v (m + 5) i j : ℤ) - 6 * (v (m + 3) i j : ℤ) + 2 * (v (m + 2) i j : ℤ) + 2 * (v (m + 1) i j : ℤ) - (v m i j : ℤ)

lemma err_base : ∀ i j : Fin 8, err 0 i j = 0 := by
  intro i j
  change (v 8 i j : ℤ) - 2 * (v 7 i j : ℤ) - 2 * (v 6 i j : ℤ) + 6 * (v 5 i j : ℤ) - 6 * (v 3 i j : ℤ) + 2 * (v 2 i j : ℤ) + 2 * (v 1 i j : ℤ) - (v 0 i j : ℤ) = 0
  simp only [v_8, v_7, v_6, v_5, v_3, v_2, v_1, v_0]
  revert i j; decide

lemma err_succ (m : ℕ) (i j : Fin 8) :
    err (m + 1) i j = if ok1 i then ∑ l : Fin 8, if ok3 i j l then err m j l else 0 else 0 := by
  have hV : ∀ r, (v (r + 1) i j : ℤ) =
      if ok1 i then ∑ l : Fin 8, if ok3 i j l then (v r j l : ℤ) else 0 else 0 := by
    intro r; rw [v, step]; split_ifs <;> simp
  unfold err
  simp only [hV]
  by_cases hi : ok1 i
  · simp only [hi, ↓reduceIte]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  · simp [hi]

lemma err_ge_zero (m : ℕ) (i j : Fin 8) : err (m + 0) i j = 0 := by
  induction m generalizing i j with
  | zero => simpa using err_base i j
  | succ m ih =>
    rw [show m + 1 + 0 = (m + 0) + 1 by omega, err_succ]
    split_ifs
    · exact Finset.sum_eq_zero (fun l _ => by have hm := ih j l; simp only [Nat.add_zero] at hm; simp [hm])
    · rfl

lemma a_rec_ge (m : ℕ) :
    (a (m + 10) : ℤ) = 2 * a (m + 9) + 2 * a (m + 8) - 6 * a (m + 7) + 6 * a (m + 5) - 2 * a (m + 4) - 2 * a (m + 3) + a (m + 2) := by
  have h : ∑ i : Fin 8, ∑ j : Fin 8, err (m + 0) i j = 0 :=
    Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => err_ge_zero m i j))
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  simp only [a_add2, Nat.cast_sum]
  have h1 : ∀ r : ℕ, m + 0 + r = m + (0 + r) := fun r => by omega
  simp only [h1, Nat.zero_add, Nat.add_zero] at h
  linarith

lemma a_zero : a 0 = 0 := rfl
lemma a_1 : a 1 = 6 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ_card]
  rw [← (Equiv.funUnique (Fin 1) Slice).symm.sum_comp]
  have hv : ∀ r : Slice, isValidS 1 ((Equiv.funUnique (Fin 1) Slice).symm r) ↔ sliceOk r := by
    intro r; unfold isValidS; constructor
    · intro h; simpa using h.1 0
    · intro hr; refine ⟨fun i => by simpa [Fin.eq_zero i] using hr, fun i => Fin.elim0 i⟩
  simp only [hv]
  rw [← rowEquiv.symm.sum_comp]
  decide
lemma a_2 : a 2 = 36 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, a_add2]
  simp only [v_0]; decide
lemma a_3 : a 3 = 90 := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, a_add2]
  simp only [v_1]; decide
lemma a_4 : a 4 = 225 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, a_add2]
  simp only [v_2]; decide
lemma a_5 : a 5 = 420 := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, a_add2]
  simp only [v_3]; decide
lemma a_6 : a 6 = 784 := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, a_add2]
  simp only [v_4]; decide
lemma a_7 : a 7 = 1260 := by
  rw [show (7 : ℕ) = 5 + 2 from rfl, a_add2]
  simp only [v_5]; decide
lemma a_8 : a 8 = 2025 := by
  rw [show (8 : ℕ) = 6 + 2 from rfl, a_add2]
  simp only [v_6]; decide
lemma a_9 : a 9 = 2970 := by
  rw [show (9 : ℕ) = 7 + 2 from rfl, a_add2]
  simp only [v_7]; decide

theorem main_proof_ours :
    (∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3) =
      X * (6 + 24 * X + 6 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + X ^ 7)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * n ^ 3 + 13 * n ^ 2 + 12 * n + 4) / 4) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * n ^ 3 + 11 * n ^ 2 + 6 * n) / 4) := by
  have hrec : ∀ n : ℕ, 9 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8) := by
    intro n hn
    rcases Nat.lt_or_ge n 10 with hlt | hge
    · interval_cases n <;> simp [a_zero, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3) =
      X * (6 + 24 * X + 6 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) ^ 3) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 8) := by
      simp only [map_ofNat, map_one]; try ring
    have hr : (X * (6 + 24 * X + 6 * X ^ 2 + 9 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + X ^ 7) : PowerSeries ℚ) =
        C (6 : ℚ) * X ^ 1 + C (24 : ℚ) * X ^ 2 + C (6 : ℚ) * X ^ 3 + C (9 : ℚ) * X ^ 4 + C (6 : ℚ) * X ^ 5 - C (2 : ℚ) * X ^ 6 - C (2 : ℚ) * X ^ 7 + C (1 : ℚ) * X ^ 8 := by
      simp only [map_ofNat, map_one]; try ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 9 with hn | hn
    · interval_cases n <;> simp [a_zero, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> try norm_num
    · have hq : (a n : ℚ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8) := by
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
      simp only [c1, c2, c3, c4, c5, c6, c7, c8, e1, e2, e3, e4, e5, e6, e7, e8, coeff_C, if_true, if_false]
      rw [hq]; ring
  have hboth : ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = if n % 2 = 0 then ((n : ℚ) ^ 4 + 6 * n ^ 3 + 13 * n ^ 2 + 12 * n + 4) / 4
        else ((n : ℚ) ^ 4 + 6 * n ^ 3 + 11 * n ^ 2 + 6 * n) / 4 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.lt_or_ge n 9 with hlt | hge
      · interval_cases n <;> simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> norm_num
      · have hq : (a n : ℚ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) +
            6 * a (n - 5) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8) := by
          exact_mod_cast hrec n hge
        rw [hq, ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega),
          ih (n - 3) (by omega) (by omega), ih (n - 5) (by omega) (by omega),
          ih (n - 6) (by omega) (by omega), ih (n - 7) (by omega) (by omega),
          ih (n - 8) (by omega) (by omega)]
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
        simp only [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
          show m + 9 - 3 = m + 6 by omega, show m + 9 - 5 = m + 4 by omega,
          show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega,
          show m + 9 - 8 = m + 1 by omega]
        rcases Nat.mod_two_eq_zero_or_one m with hm | hm
        · simp only [show (m + 9) % 2 = 1 by omega, show (m + 8) % 2 = 0 by omega,
            show (m + 7) % 2 = 1 by omega, show (m + 6) % 2 = 0 by omega,
            show (m + 4) % 2 = 0 by omega, show (m + 3) % 2 = 1 by omega,
            show (m + 2) % 2 = 0 by omega, show (m + 1) % 2 = 1 by omega]
          norm_num; push_cast; ring
        · simp only [show (m + 9) % 2 = 0 by omega, show (m + 8) % 2 = 1 by omega,
            show (m + 7) % 2 = 0 by omega, show (m + 6) % 2 = 1 by omega,
            show (m + 4) % 2 = 1 by omega, show (m + 3) % 2 = 0 by omega,
            show (m + 2) % 2 = 1 by omega, show (m + 1) % 2 = 0 by omega]
          norm_num; push_cast; ring
  have hextra :
      (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * n ^ 3 + 13 * n ^ 2 + 12 * n + 4) / 4) ∧
      (∀ n : ℕ, Odd n → (a n : ℚ) = ((n : ℚ) ^ 4 + 6 * n ^ 3 + 11 * n ^ 2 + 6 * n) / 4) := by
    refine ⟨fun n hn he => ?_, fun n ho => ?_⟩
    · have hm : n % 2 = 0 := Nat.even_iff.mp he
      simpa [hm] using hboth n hn
    · have hm : n % 2 = 1 := Nat.odd_iff.mp ho
      have hn : 1 ≤ n := by omega
      simpa [hm] using hboth n hn
  refine ⟨hrec, hgf, hextra⟩


lemma rowT : ∀ p q r : Fin 2,
    ((((p : ℕ), (q : ℕ), (r : ℕ)) ≠ (0, 0, 0) ∧ ((p : ℕ), (q : ℕ), (r : ℕ)) ≠ (0, 1, 1)) ↔
      ((p, q, r) ≠ (0, 0, 0) ∧ (p, q, r) ≠ (0, 1, 1))) := by decide

lemma colT : ∀ p q r : Fin 2,
    ((((p : ℕ), (q : ℕ), (r : ℕ)) ≠ (0, 0, 1) ∧ ((p : ℕ), (q : ℕ), (r : ℕ)) ≠ (0, 1, 1)) ↔
      ((p, q, r) ≠ (0, 0, 1) ∧ (p, q, r) ≠ (0, 1, 1))) := by decide

lemma hget {n : ℕ} (x : Fin n → Fin 3 → Fin 2) (i j : ℕ) (hi : i < n) (hj : j < 3) :
    OMA.S_oeis_a207363.get x i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  simp [OMA.S_oeis_a207363.get, hi, hj]

lemma valid_iff (n : ℕ) (x : Fin n → Fin 3 → Fin 2) :
    OMA.S_oeis_a207363.avoids x = true ↔ isValid n x := by
  unfold OMA.S_oeis_a207363.avoids
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hr, hc⟩
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · have := hr i.val i.isLt 0 (by norm_num)
      rw [hget x i.val 0 i.isLt (by norm_num), hget x i.val (0 + 1) i.isLt (by norm_num),
        hget x i.val (0 + 2) i.isLt (by norm_num)] at this
      exact (rowT _ _ _).mp this
    · have := hc i.val i.isLt j.val j.isLt
      rw [hget x i.val j.val (by omega) j.isLt, hget x (i.val + 1) j.val (by omega) j.isLt,
        hget x (i.val + 2) j.val (by omega) j.isLt] at this
      exact (colT _ _ _).mp this
  · rintro ⟨hr, hc⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · obtain rfl : j = 0 := by omega
      rw [hget x i 0 hi (by norm_num), hget x i (0 + 1) hi (by norm_num),
        hget x i (0 + 2) hi (by norm_num)]
      exact (rowT _ _ _).mpr (hr ⟨i, hi⟩)
    · rw [hget x i j (by omega) hj, hget x (i + 1) j (by omega) hj,
        hget x (i + 2) j (by omega) hj]
      exact (colT _ _ _).mpr (hc ⟨i, by omega⟩ ⟨j, hj⟩)

lemma a_eq (m : ℕ) : (OMA.S_oeis_a207363.a (m + 1) : ℚ) = (a (m + 1) : ℚ) := by
  unfold OMA.S_oeis_a207363.a
  show (((Finset.univ.filter fun x : Fin (m + 1) → Fin 3 → Fin 2 =>
      OMA.S_oeis_a207363.avoids x = true).card : ℤ) : ℚ) =
    ((Finset.univ.filter (isValid (m + 1))).card : ℚ)
  rw [Int.cast_natCast]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact valid_iff (m + 1) x

theorem main_proof : type_of% @OMA.S_oeis_a207363.main := by
  obtain ⟨_, hgf, hev, hod⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n < 1 then 0 else (OMA.S_oeis_a207363.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → (OMA.S_oeis_a207363.a n : ℚ) = (a n : ℚ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨by rw [hser]; exact hgf, fun n hn h2 => ?_, fun n hn h2 => ?_⟩
  · rw [hA n hn]; exact hev n hn h2
  · rw [hA n hn]; exact hod n h2

end OMA.P207363

theorem OMA.solution : type_of% @OMA.S_oeis_a207363.main := OMA.P207363.main_proof
