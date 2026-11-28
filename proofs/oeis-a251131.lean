import OMAStatements.S_oeis_a251131

-- Credit: @Dariusthedoggie
-- Proof: 27-state transfer matrix over length-3 rows of (n+1) X 3 0..2 arrays; transition operator annihilates the order-7 recurrence polynomial (shift k=3), yielding the recurrence, generating function, and closed form.

namespace OMA.P251131

open OMA.S_oeis_a251131 PowerSeries

abbrev Row := Fin 3 → Fin 3

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 2, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 27 :=
  ⟨9 * (r 0).val + 3 * (r 1).val + (r 2).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega⟩

def dec (k : Fin 27) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 9, by omega⟩
  else if c.val = 1 then ⟨(k.val / 3) % 3, by omega⟩
  else ⟨k.val % 3, by omega⟩

lemma enc_dec : ∀ k : Fin 27, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 27) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 27) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 27) : ℕ := match i.val with
  | 0 => 124006913
  | 1 => 124532227
  | 2 => 133987847
  | 3 => 52432904
  | 4 => 52695561
  | 5 => 57423387
  | 6 => 16810048
  | 7 => 16810048
  | 8 => 19173961
  | 9 => 6554112
  | 10 => 7079424
  | 11 => 16518656
  | 12 => 2097152
  | 13 => 2359809
  | 14 => 7079427
  | 15 => 0
  | 16 => 0
  | 17 => 2363913
  | 18 => 262144
  | 19 => 786432
  | 20 => 1835008
  | 21 => 0
  | 22 => 262144
  | 23 => 786432
  | 24 => 0
  | 25 => 0
  | 26 => 262657
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 27, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 27 → ℕ) (i : Fin 27) : ℕ :=
  ∑ j : Fin 27, if ok2 i j then f j else 0

def v : ℕ → Fin 27 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 27, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 27, if enc (y 0) = i then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0))]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · exact Finset.sum_comm

lemma isValid_zero (y : Fin 1 → Row) : isValid 0 y := by
  intro i; exact Fin.elim0 i

lemma isValid_cons (m : ℕ) (r : Row) (y : Fin (m + 1) → Row) :
    isValid (m + 1) (Fin.cons r y) ↔ okRow r (y 0) ∧ isValid m y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h 0 j
    · intro i j
      simpa using h i.succ j
  · rintro ⟨h0, hy⟩ i j
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h0 j
    · simpa using hy i' j

lemma v_eq (m : ℕ) (i : Fin 27) :
    v m i = ∑ y : Fin (m + 1) → Row, if enc (y 0) = i ∧ isValid m y then 1 else 0 := by
  induction m generalizing i with
  | zero =>
    rw [v, ← (Equiv.funUnique (Fin 1) Row).symm.sum_comp]
    rw [Finset.sum_eq_single (dec i)]
    · have hu : (Equiv.funUnique (Fin 1) Row).symm (dec i) = fun _ : Fin 1 => dec i := funext fun _ => rfl
      rw [hu]
      simp [enc_dec, isValid_zero]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      have hu : (Equiv.funUnique (Fin 1) Row).symm r = fun _ : Fin 1 => r := funext fun _ => rfl
      rw [hu]
      simp [hne]
    · simp
  | succ m ih =>
    rw [v, step, sum_cons]
    rw [Finset.sum_eq_single (dec i)]
    · simp only [Fin.cons_zero, enc_dec, true_and, isValid_cons]
      rw [fiber]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j]
      by_cases h : ok2 i j
      · simp only [h, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : enc (y 0) = j
        · have hok : okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hok]
        · simp [hy]
      · simp only [h, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : enc (y 0) = j
        · have hnok : ¬ okRow (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hnok]
        · simp [hy]
    · intro r _ hr
      have hne : enc r ≠ i := fun h => hr (by rw [← dec_enc r, h])
      apply Finset.sum_eq_zero
      intro y _
      simp [hne]
    · simp

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 27, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 27) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 1
  | 12 => 1
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 1
  | 17 => 1
  | 18 => 1
  | 19 => 1
  | 20 => 1
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 1
  | 25 => 1
  | 26 => 1
  | _ => 0

def vtab1 (i : Fin 27) : ℕ := match i.val with
  | 0 => 10
  | 1 => 13
  | 2 => 18
  | 3 => 5
  | 4 => 8
  | 5 => 14
  | 6 => 3
  | 7 => 3
  | 8 => 9
  | 9 => 4
  | 10 => 6
  | 11 => 9
  | 12 => 1
  | 13 => 4
  | 14 => 8
  | 15 => 0
  | 16 => 0
  | 17 => 6
  | 18 => 1
  | 19 => 2
  | 20 => 3
  | 21 => 0
  | 22 => 1
  | 23 => 2
  | 24 => 0
  | 25 => 0
  | 26 => 3
  | _ => 0

def vtab2 (i : Fin 27) : ℕ := match i.val with
  | 0 => 24
  | 1 => 45
  | 2 => 85
  | 3 => 6
  | 4 => 21
  | 5 => 55
  | 6 => 3
  | 7 => 3
  | 8 => 24
  | 9 => 6
  | 10 => 14
  | 11 => 28
  | 12 => 0
  | 13 => 15
  | 14 => 37
  | 15 => 0
  | 16 => 0
  | 17 => 21
  | 18 => 1
  | 19 => 3
  | 20 => 6
  | 21 => 0
  | 22 => 1
  | 23 => 3
  | 24 => 0
  | 25 => 0
  | 26 => 15
  | _ => 0

def vtab3 (i : Fin 27) : ℕ := match i.val with
  | 0 => 62
  | 1 => 124
  | 2 => 283
  | 3 => 6
  | 4 => 37
  | 5 => 136
  | 6 => 3
  | 7 => 3
  | 8 => 40
  | 9 => 8
  | 10 => 25
  | 11 => 62
  | 12 => 0
  | 13 => 31
  | 14 => 94
  | 15 => 0
  | 16 => 0
  | 17 => 37
  | 18 => 1
  | 19 => 4
  | 20 => 10
  | 21 => 0
  | 22 => 1
  | 23 => 4
  | 24 => 0
  | 25 => 0
  | 26 => 31
  | _ => 0

def vtab4 (i : Fin 27) : ℕ := match i.val with
  | 0 => 134
  | 1 => 287
  | 2 => 740
  | 3 => 6
  | 4 => 77
  | 5 => 299
  | 6 => 3
  | 7 => 3
  | 8 => 80
  | 9 => 10
  | 10 => 39
  | 11 => 115
  | 12 => 0
  | 13 => 71
  | 14 => 225
  | 15 => 0
  | 16 => 0
  | 17 => 77
  | 18 => 1
  | 19 => 5
  | 20 => 15
  | 21 => 0
  | 22 => 1
  | 23 => 5
  | 24 => 0
  | 25 => 0
  | 26 => 71
  | _ => 0

def vtab5 (i : Fin 27) : ℕ := match i.val with
  | 0 => 288
  | 1 => 619
  | 2 => 1719
  | 3 => 6
  | 4 => 151
  | 5 => 631
  | 6 => 3
  | 7 => 3
  | 8 => 154
  | 9 => 12
  | 10 => 56
  | 11 => 191
  | 12 => 0
  | 13 => 145
  | 14 => 477
  | 15 => 0
  | 16 => 0
  | 17 => 151
  | 18 => 1
  | 19 => 6
  | 20 => 21
  | 21 => 0
  | 22 => 1
  | 23 => 6
  | 24 => 0
  | 25 => 0
  | 26 => 145
  | _ => 0

def vtab6 (i : Fin 27) : ℕ := match i.val with
  | 0 => 592
  | 1 => 1273
  | 2 => 3687
  | 3 => 6
  | 4 => 307
  | 5 => 1285
  | 6 => 3
  | 7 => 3
  | 8 => 310
  | 9 => 14
  | 10 => 76
  | 11 => 294
  | 12 => 0
  | 13 => 301
  | 14 => 983
  | 15 => 0
  | 16 => 0
  | 17 => 307
  | 18 => 1
  | 19 => 7
  | 20 => 28
  | 21 => 0
  | 22 => 1
  | 23 => 7
  | 24 => 0
  | 25 => 0
  | 26 => 301
  | _ => 0

def vtab7 (i : Fin 27) : ℕ := match i.val with
  | 0 => 1210
  | 1 => 2566
  | 2 => 7565
  | 3 => 6
  | 4 => 613
  | 5 => 2578
  | 6 => 3
  | 7 => 3
  | 8 => 616
  | 9 => 16
  | 10 => 99
  | 11 => 428
  | 12 => 0
  | 13 => 607
  | 14 => 1964
  | 15 => 0
  | 16 => 0
  | 17 => 613
  | 18 => 1
  | 19 => 8
  | 20 => 36
  | 21 => 0
  | 22 => 1
  | 23 => 8
  | 24 => 0
  | 25 => 0
  | 26 => 607
  | _ => 0

def vtab8 (i : Fin 27) : ℕ := match i.val with
  | 0 => 2442
  | 1 => 5115
  | 2 => 15116
  | 3 => 6
  | 4 => 1233
  | 5 => 5127
  | 6 => 3
  | 7 => 3
  | 8 => 1236
  | 9 => 18
  | 10 => 125
  | 11 => 597
  | 12 => 0
  | 13 => 1227
  | 14 => 3901
  | 15 => 0
  | 16 => 0
  | 17 => 1233
  | 18 => 1
  | 19 => 9
  | 20 => 45
  | 21 => 0
  | 22 => 1
  | 23 => 9
  | 24 => 0
  | 25 => 0
  | 26 => 1227
  | _ => 0

def vtab9 (i : Fin 27) : ℕ := match i.val with
  | 0 => 4916
  | 1 => 10165
  | 2 => 29833
  | 3 => 6
  | 4 => 2467
  | 5 => 10177
  | 6 => 3
  | 7 => 3
  | 8 => 2470
  | 9 => 20
  | 10 => 154
  | 11 => 805
  | 12 => 0
  | 13 => 2461
  | 14 => 7711
  | 15 => 0
  | 16 => 0
  | 17 => 2467
  | 18 => 1
  | 19 => 10
  | 20 => 55
  | 21 => 0
  | 22 => 1
  | 23 => 10
  | 24 => 0
  | 25 => 0
  | 26 => 2461
  | _ => 0

def vtab10 (i : Fin 27) : ℕ := match i.val with
  | 0 => 9860
  | 1 => 20189
  | 2 => 58603
  | 3 => 6
  | 4 => 4943
  | 5 => 20201
  | 6 => 3
  | 7 => 3
  | 8 => 4946
  | 9 => 22
  | 10 => 186
  | 11 => 1056
  | 12 => 0
  | 13 => 4937
  | 14 => 15267
  | 15 => 0
  | 16 => 0
  | 17 => 4943
  | 18 => 1
  | 19 => 11
  | 20 => 66
  | 21 => 0
  | 22 => 1
  | 23 => 11
  | 24 => 0
  | 25 => 0
  | 26 => 4937
  | _ => 0

lemma v_0 : ∀ i : Fin 27, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 27, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 27, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 27, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 27, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 27, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel
lemma v_6 : ∀ i : Fin 27, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel
lemma v_7 : ∀ i : Fin 27, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 27, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel
lemma v_9 : ∀ i : Fin 27, v 9 i = vtab9 i := by
  intro i; rw [show (9 : ℕ) = 8 + 1 from rfl, v, step]; simp only [v_8, ok2_iff]; revert i; decide +kernel
lemma v_10 : ∀ i : Fin 27, v 10 i = vtab10 i := by
  intro i; rw [show (10 : ℕ) = 9 + 1 from rfl, v, step]; simp only [v_9, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 27) : ℤ :=
  (v (m + 7) i : ℤ) - 6 * (v (m + 6) i : ℤ) + 13 * (v (m + 5) i : ℤ) - 10 * (v (m + 4) i : ℤ) - 5 * (v (m + 3) i : ℤ) + 14 * (v (m + 2) i : ℤ) - 9 * (v (m + 1) i : ℤ) + 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 27, err 3 i = 0 := by
  intro i
  change (v 10 i : ℤ) - 6 * (v 9 i : ℤ) + 13 * (v 8 i : ℤ) - 10 * (v 7 i : ℤ) - 5 * (v 6 i : ℤ) + 14 * (v 5 i : ℤ) - 9 * (v 4 i : ℤ) + 2 * (v 3 i : ℤ) = 0
  simp only [v_10, v_9, v_8, v_7, v_6, v_5, v_4, v_3]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 27) :
    err (m + 1) i = ∑ j : Fin 27, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 27, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 27) : err (m + 3) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 3 = (m + 3) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 10) : ℤ) = 6 * a (m + 9) - 13 * a (m + 8) + 10 * a (m + 7) + 5 * a (m + 6) - 14 * a (m + 5) + 9 * a (m + 4) - 2 * a (m + 3) := by
  have h : ∑ i : Fin 27, err (m + 3) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 27, (v (m + 3 + r) i : ℤ)) = (a (m + 3 + r) : ℤ) := by
    intro r
    have h1 : m + 3 + r = (m + 2 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 27, (v (m + 3) i : ℤ)) = (a (m + 3) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 3 + 1 = m + 4 := by omega
  have h2_2 : m + 3 + 2 = m + 5 := by omega
  have h2_3 : m + 3 + 3 = m + 6 := by omega
  have h2_4 : m + 3 + 4 = m + 7 := by omega
  have h2_5 : m + 3 + 5 = m + 8 := by omega
  have h2_6 : m + 3 + 6 = m + 9 := by omega
  have h2_7 : m + 3 + 7 = m + 10 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 133 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 1 i = 133
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 416 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 2 i = 416
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 1002 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 3 i = 1002
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 2264 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 4 i = 2264
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 4786 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 5 i = 4786
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 9786 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 6 i = 9786
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 19548 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 7 i = 19548
  simp only [v_7]; decide +kernel
lemma a_8 : a 8 = 38674 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 8 i = 38674
  simp only [v_8]; decide +kernel
lemma a_9 : a 9 = 76196 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 9 i = 76196
  simp only [v_9]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (-873 + 49 * (-1 : ℚ) ^ n + 841 * (2 : ℚ) ^ (1 + n) - 614 * n - 11 * (n : ℚ) ^ 2 + 38 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12

theorem main_proof :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
      X * (133 - 382 * X + 235 * X ^ 2 + 330 * X ^ 3 - 597 * X ^ 4 + 264 * X ^ 5 + 27 * X ^ 6 - 26 * X ^ 7 - 4 * X ^ 8)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (-873 + 49 * (-1 : ℚ) ^ n + 841 * (2 : ℚ) ^ (1 + n) - 614 * n - 11 * (n : ℚ) ^ 2 + 38 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12) := by
  have hrec : ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
      X * (133 - 382 * X + 235 * X ^ 2 + 330 * X ^ 3 - 597 * X ^ 4 + 264 * X ^ 5 + 27 * X ^ 6 - 26 * X ^ 7 - 4 * X ^ 8) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (13 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        + C (14 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        - C (9 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (133 - 382 * X + 235 * X ^ 2 + 330 * X ^ 3 - 597 * X ^ 4 + 264 * X ^ 5 + 27 * X ^ 6 - 26 * X ^ 7 - 4 * X ^ 8) : PowerSeries ℚ) =
        C (133 : ℚ) * X ^ 1 - C (382 : ℚ) * X ^ 2 + C (235 : ℚ) * X ^ 3 + C (330 : ℚ) * X ^ 4 - C (597 : ℚ) * X ^ 5 + C (264 : ℚ) * X ^ 6 + C (27 : ℚ) * X ^ 7 - C (26 : ℚ) * X ^ 8 - C (4 : ℚ) * X ^ 9 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 10 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9] <;> try norm_num
    · have hq : (a n : ℚ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have c5 : 5 ≤ n := by omega
      have c6 : 6 ≤ n := by omega
      have c7 : 7 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      have e6 : n - 6 ≠ 0 := by omega
      have e7 : n - 7 ≠ 0 := by omega
      have e8 : n - 8 ≠ 0 := by omega
      have e9 : n - 9 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, c5, c6, c7, e1, e2, e3, e4, e5, e6, e7, e8, e9, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (-873 + 49 * (-1 : ℚ) ^ n + 841 * (2 : ℚ) ^ (1 + n) - 614 * n - 11 * (n : ℚ) ^ 2 + 38 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12 := by
    have hQ : ∀ m : ℕ,
                (a (m + 3) : ℚ) = cf (m + 3) ∧
        (a (m + 4) : ℚ) = cf (m + 4) ∧
        (a (m + 5) : ℚ) = cf (m + 5) ∧
        (a (m + 6) : ℚ) = cf (m + 6) ∧
        (a (m + 7) : ℚ) = cf (m + 7) ∧
        (a (m + 8) : ℚ) = cf (m + 8) ∧
        (a (m + 9) : ℚ) = cf (m + 9) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add, cf, a_3, a_4, a_5, a_6, a_7, a_8, a_9]
        norm_num
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 3 = m + 4 by omega] using h1), (by simpa only [show m + 1 + 4 = m + 5 by omega] using h2), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h3), (by simpa only [show m + 1 + 6 = m + 7 by omega] using h4), (by simpa only [show m + 1 + 7 = m + 8 by omega] using h5), (by simpa only [show m + 1 + 8 = m + 9 by omega] using h6), ?_⟩
        rw [show m + 1 + 9 = m + 10 by omega]
        have hr : (a (m + 10) : ℚ) = 6 * a (m + 9) - 13 * a (m + 8) + 10 * a (m + 7) + 5 * a (m + 6) - 14 * a (m + 5) + 9 * a (m + 4) - 2 * a (m + 3) := by
          have h0' := hrec (m + 10) (by omega)
          simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h6, h5, h4, h3, h2, h1, h0]
        unfold cf
        have hp0_1 : (-1 : ℚ) ^ (m + 4) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 1 := by rw [show m + 4 = (m + 3) + 1 by omega, pow_add]
        have hp0_2 : (-1 : ℚ) ^ (m + 5) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 2 := by rw [show m + 5 = (m + 3) + 2 by omega, pow_add]
        have hp0_3 : (-1 : ℚ) ^ (m + 6) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 3 := by rw [show m + 6 = (m + 3) + 3 by omega, pow_add]
        have hp0_4 : (-1 : ℚ) ^ (m + 7) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 4 := by rw [show m + 7 = (m + 3) + 4 by omega, pow_add]
        have hp0_5 : (-1 : ℚ) ^ (m + 8) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 5 := by rw [show m + 8 = (m + 3) + 5 by omega, pow_add]
        have hp0_6 : (-1 : ℚ) ^ (m + 9) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 6 := by rw [show m + 9 = (m + 3) + 6 by omega, pow_add]
        have hp0_7 : (-1 : ℚ) ^ (m + 10) = (-1 : ℚ) ^ (m + 3) * (-1 : ℚ) ^ 7 := by rw [show m + 10 = (m + 3) + 7 by omega, pow_add]
        have hp1_1 : (2 : ℚ) ^ (1 + (m + 4)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 1 := by rw [show 1 + (m + 4) = (1 + (m + 3)) + 1 by omega, pow_add]
        have hp1_2 : (2 : ℚ) ^ (1 + (m + 5)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 2 := by rw [show 1 + (m + 5) = (1 + (m + 3)) + 2 by omega, pow_add]
        have hp1_3 : (2 : ℚ) ^ (1 + (m + 6)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 3 := by rw [show 1 + (m + 6) = (1 + (m + 3)) + 3 by omega, pow_add]
        have hp1_4 : (2 : ℚ) ^ (1 + (m + 7)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 4 := by rw [show 1 + (m + 7) = (1 + (m + 3)) + 4 by omega, pow_add]
        have hp1_5 : (2 : ℚ) ^ (1 + (m + 8)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 5 := by rw [show 1 + (m + 8) = (1 + (m + 3)) + 5 by omega, pow_add]
        have hp1_6 : (2 : ℚ) ^ (1 + (m + 9)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 6 := by rw [show 1 + (m + 9) = (1 + (m + 3)) + 6 by omega, pow_add]
        have hp1_7 : (2 : ℚ) ^ (1 + (m + 10)) = (2 : ℚ) ^ (1 + (m + 3)) * (2 : ℚ) ^ 7 := by rw [show 1 + (m + 10) = (1 + (m + 3)) + 7 by omega, pow_add]
        simp only [hp0_1, hp0_2, hp0_3, hp0_4, hp0_5, hp0_6, hp0_7, hp1_1, hp1_2, hp1_3, hp1_4, hp1_5, hp1_6, hp1_7]
        push_cast
        ring
    intro n hn
    have h := (hQ (n - 3)).1
    rw [show n - 3 + 3 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩

end OMA.P251131

theorem OMA.solution : type_of% @OMA.S_oeis_a251131.main := OMA.P251131.main_proof
