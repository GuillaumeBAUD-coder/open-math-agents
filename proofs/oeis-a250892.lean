import OMAStatements.S_oeis_a250892

-- Credit: @Dariusthedoggie
-- Proof: row transfer matrix annihilated by the order-7 recurrence polynomial, giving recurrence, g.f. and closed form, bridged to the Nat.card encoding.

namespace OMA.P250892

open PowerSeries
/-- A `2 X 2` `0..2` subblock `(a, b / c, d)` has `b - a ≤ d - c` and `|c - a| ≤ |d - b|` (in `ℤ`). -/
def okBlock (a b c d : Fin 3) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 3` `0..2` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 2,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250892: Number of (n+1) X (2+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

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
  | 0 => 67264823
  | 1 => 16422
  | 2 => 4
  | 3 => 197048
  | 4 => 131376
  | 5 => 32
  | 6 => 448
  | 7 => 384
  | 8 => 256
  | 9 => 79851312
  | 10 => 8408096
  | 11 => 2048
  | 12 => 100888966
  | 13 => 67264773
  | 14 => 16386
  | 15 => 229424
  | 16 => 196648
  | 17 => 131088
  | 18 => 81682688
  | 19 => 9977856
  | 20 => 1048576
  | 21 => 115543040
  | 22 => 79825408
  | 23 => 8389632
  | 24 => 117465092
  | 25 => 100683776
  | 26 => 67117057
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
  | 1 => 4
  | 2 => 1
  | 3 => 7
  | 4 => 4
  | 5 => 1
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | 9 => 12
  | 10 => 5
  | 11 => 1
  | 12 => 11
  | 13 => 7
  | 14 => 2
  | 15 => 5
  | 16 => 4
  | 17 => 2
  | 18 => 10
  | 19 => 4
  | 20 => 1
  | 21 => 9
  | 22 => 6
  | 23 => 2
  | 24 => 6
  | 25 => 4
  | 26 => 3
  | _ => 0

def vtab2 (i : Fin 27) : ℕ := match i.val with
  | 0 => 35
  | 1 => 8
  | 2 => 1
  | 3 => 21
  | 4 => 8
  | 5 => 1
  | 6 => 6
  | 7 => 3
  | 8 => 1
  | 9 => 46
  | 10 => 11
  | 11 => 1
  | 12 => 41
  | 13 => 26
  | 14 => 6
  | 15 => 16
  | 16 => 14
  | 17 => 6
  | 18 => 38
  | 19 => 9
  | 20 => 1
  | 21 => 36
  | 22 => 26
  | 23 => 7
  | 24 => 23
  | 25 => 20
  | 26 => 20
  | _ => 0

def vtab3 (i : Fin 27) : ℕ := match i.val with
  | 0 => 112
  | 1 => 16
  | 2 => 1
  | 3 => 54
  | 4 => 16
  | 5 => 1
  | 6 => 10
  | 7 => 4
  | 8 => 1
  | 9 => 159
  | 10 => 26
  | 11 => 1
  | 12 => 146
  | 13 => 95
  | 14 => 14
  | 15 => 45
  | 16 => 42
  | 17 => 14
  | 18 => 140
  | 19 => 23
  | 20 => 1
  | 21 => 141
  | 22 => 106
  | 23 => 18
  | 24 => 96
  | 25 => 87
  | 26 => 81
  | _ => 0

def vtab4 (i : Fin 27) : ℕ := match i.val with
  | 0 => 351
  | 1 => 32
  | 2 => 1
  | 3 => 132
  | 4 => 32
  | 5 => 1
  | 6 => 15
  | 7 => 5
  | 8 => 1
  | 9 => 532
  | 10 => 60
  | 11 => 1
  | 12 => 501
  | 13 => 318
  | 14 => 30
  | 15 => 118
  | 16 => 111
  | 17 => 30
  | 18 => 493
  | 19 => 56
  | 20 => 1
  | 21 => 516
  | 22 => 379
  | 23 => 44
  | 24 => 374
  | 25 => 328
  | 26 => 288
  | _ => 0

def vtab5 (i : Fin 27) : ℕ := match i.val with
  | 0 => 1084
  | 1 => 64
  | 2 => 1
  | 3 => 312
  | 4 => 64
  | 5 => 1
  | 6 => 21
  | 7 => 6
  | 8 => 1
  | 9 => 1716
  | 10 => 136
  | 11 => 1
  | 12 => 1645
  | 13 => 1019
  | 14 => 62
  | 15 => 292
  | 16 => 274
  | 17 => 62
  | 18 => 1640
  | 19 => 131
  | 20 => 1
  | 21 => 1757
  | 22 => 1274
  | 23 => 104
  | 24 => 1339
  | 25 => 1147
  | 26 => 957
  | _ => 0

def vtab6 (i : Fin 27) : ℕ := match i.val with
  | 0 => 3315
  | 1 => 128
  | 2 => 1
  | 3 => 720
  | 4 => 128
  | 5 => 1
  | 6 => 28
  | 7 => 7
  | 8 => 1
  | 9 => 5397
  | 10 => 304
  | 11 => 1
  | 12 => 5238
  | 13 => 3186
  | 14 => 126
  | 15 => 693
  | 16 => 649
  | 17 => 126
  | 18 => 5251
  | 19 => 298
  | 20 => 1
  | 21 => 5712
  | 22 => 4114
  | 23 => 240
  | 24 => 4525
  | 25 => 3811
  | 26 => 3060
  | _ => 0

def vtab7 (i : Fin 27) : ℕ := match i.val with
  | 0 => 10072
  | 1 => 256
  | 2 => 1
  | 3 => 1632
  | 4 => 256
  | 5 => 1
  | 6 => 36
  | 7 => 8
  | 8 => 1
  | 9 => 16684
  | 10 => 672
  | 11 => 1
  | 12 => 16333
  | 13 => 9815
  | 14 => 254
  | 15 => 1597
  | 16 => 1496
  | 17 => 254
  | 18 => 16403
  | 19 => 665
  | 20 => 1
  | 21 => 18017
  | 22 => 12938
  | 23 => 544
  | 24 => 14709
  | 25 => 12235
  | 26 => 9561
  | _ => 0

def vtab8 (i : Fin 27) : ℕ := match i.val with
  | 0 => 30471
  | 1 => 512
  | 2 => 1
  | 3 => 3648
  | 4 => 512
  | 5 => 1
  | 6 => 45
  | 7 => 9
  | 8 => 1
  | 9 => 50981
  | 10 => 1472
  | 11 => 1
  | 12 => 50214
  | 13 => 29958
  | 14 => 510
  | 15 => 3604
  | 16 => 3383
  | 17 => 510
  | 18 => 50436
  | 19 => 1464
  | 20 => 1
  | 21 => 55718
  | 22 => 39982
  | 23 => 1216
  | 24 => 46575
  | 25 => 38383
  | 26 => 29448
  | _ => 0

def vtab9 (i : Fin 27) : ℕ := match i.val with
  | 0 => 91924
  | 1 => 1024
  | 2 => 1
  | 3 => 8064
  | 4 => 1024
  | 5 => 1
  | 6 => 55
  | 7 => 10
  | 8 => 1
  | 9 => 154592
  | 10 => 3200
  | 11 => 1
  | 12 => 152929
  | 13 => 90899
  | 14 => 1022
  | 15 => 8010
  | 16 => 7542
  | 17 => 1022
  | 18 => 153526
  | 19 => 3191
  | 20 => 1
  | 21 => 170113
  | 22 => 122138
  | 23 => 2688
  | 24 => 144875
  | 25 => 118555
  | 26 => 89877
  | _ => 0

def vtab10 (i : Fin 27) : ℕ := match i.val with
  | 0 => 276795
  | 1 => 2048
  | 2 => 1
  | 3 => 17664
  | 4 => 2048
  | 5 => 1
  | 6 => 66
  | 7 => 11
  | 8 => 1
  | 9 => 466465
  | 10 => 6912
  | 11 => 1
  | 12 => 462882
  | 13 => 274746
  | 14 => 2046
  | 15 => 17599
  | 16 => 16629
  | 17 => 2046
  | 18 => 464365
  | 19 => 6902
  | 20 => 1
  | 21 => 515136
  | 22 => 370318
  | 23 => 5888
  | 24 => 445229
  | 25 => 362383
  | 26 => 272700
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
  (v (m + 7) i : ℤ) - 12 * (v (m + 6) i : ℤ) + 60 * (v (m + 5) i : ℤ) - 162 * (v (m + 4) i : ℤ) + 255 * (v (m + 3) i : ℤ) - 234 * (v (m + 2) i : ℤ) + 116 * (v (m + 1) i : ℤ) - 24 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 27, err 3 i = 0 := by
  intro i
  change (v 10 i : ℤ) - 12 * (v 9 i : ℤ) + 60 * (v 8 i : ℤ) - 162 * (v 7 i : ℤ) + 255 * (v 6 i : ℤ) - 234 * (v 5 i : ℤ) + 116 * (v 4 i : ℤ) - 24 * (v 3 i : ℤ) = 0
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
    (a (m + 10) : ℤ) = 12 * a (m + 9) - 60 * a (m + 8) + 162 * a (m + 7) - 255 * a (m + 6) + 234 * a (m + 5) - 116 * a (m + 4) + 24 * a (m + 3) := by
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
lemma a_1 : a 1 = 127 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 1 i = 127
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 431 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 2 i = 431
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 1450 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 3 i = 1450
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 4750 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 4 i = 4750
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 15111 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 5 i = 15111
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 47061 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 6 i = 47061
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 144442 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 7 i = 144442
  simp only [v_7]; decide +kernel
lemma a_8 : a 8 = 439056 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 8 i = 439056
  simp only [v_8]; decide +kernel
lemma a_9 : a 9 = 1326285 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 9 i = 1326285
  simp only [v_9]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (567 - 3807 * (2 : ℚ) ^ n + 7225 * (3 : ℚ) ^ n - 54 * (-1 + 15 * (2 : ℚ) ^ n) * (n : ℚ) + 54 * (-2 + 3 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 108


theorem main_proof_ours :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 12 * a (n - 1) - 60 * a (n - 2) + 162 * a (n - 3) - 255 * a (n - 4) + 234 * a (n - 5) - 116 * a (n - 6) + 24 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 - 2 * X) ^ 3 * (1 - 3 * X)) =
      X * (127 - 1093 * X + 3898 * X ^ 2 - 7364 * X ^ 3 + 7674 * X ^ 4 - 3984 * X ^ 5 + 498 * X ^ 6 + 328 * X ^ 7 - 88 * X ^ 8)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (567 - 3807 * (2 : ℚ) ^ n + 7225 * (3 : ℚ) ^ n - 54 * (-1 + 15 * (2 : ℚ) ^ n) * (n : ℚ) + 54 * (-2 + 3 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 108) := by
  have hrec : ∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 12 * a (n - 1) - 60 * a (n - 2) + 162 * a (n - 3) - 255 * a (n - 4) + 234 * a (n - 5) - 116 * a (n - 6) + 24 * a (n - 7) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 - 2 * X) ^ 3 * (1 - 3 * X)) =
      X * (127 - 1093 * X + 3898 * X ^ 2 - 7364 * X ^ 3 + 7674 * X ^ 4 - 3984 * X ^ 5 + 498 * X ^ 6 + 328 * X ^ 7 - 88 * X ^ 8) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 - 2 * X) ^ 3 * (1 - 3 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (12 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (60 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (162 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (255 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (234 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        + C (116 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        - C (24 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (127 - 1093 * X + 3898 * X ^ 2 - 7364 * X ^ 3 + 7674 * X ^ 4 - 3984 * X ^ 5 + 498 * X ^ 6 + 328 * X ^ 7 - 88 * X ^ 8) : PowerSeries ℚ) =
        C (127 : ℚ) * X ^ 1 - C (1093 : ℚ) * X ^ 2 + C (3898 : ℚ) * X ^ 3 - C (7364 : ℚ) * X ^ 4 + C (7674 : ℚ) * X ^ 5 - C (3984 : ℚ) * X ^ 6 + C (498 : ℚ) * X ^ 7 + C (328 : ℚ) * X ^ 8 - C (88 : ℚ) * X ^ 9 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 10 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9] <;> try norm_num
    · have hq : (a n : ℚ) = 12 * a (n - 1) - 60 * a (n - 2) + 162 * a (n - 3) - 255 * a (n - 4) + 234 * a (n - 5) - 116 * a (n - 6) + 24 * a (n - 7) := by
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
  have hcf : ∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (567 - 3807 * (2 : ℚ) ^ n + 7225 * (3 : ℚ) ^ n - 54 * (-1 + 15 * (2 : ℚ) ^ n) * (n : ℚ) + 54 * (-2 + 3 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 108 := by
    have hb_3 : (a 3 : ℚ) = cf 3 := by
      rw [a_3]; unfold cf
      push_cast
      norm_num
    have hb_4 : (a 4 : ℚ) = cf 4 := by
      rw [a_4]; unfold cf
      push_cast
      norm_num
    have hb_5 : (a 5 : ℚ) = cf 5 := by
      rw [a_5]; unfold cf
      push_cast
      norm_num
    have hb_6 : (a 6 : ℚ) = cf 6 := by
      rw [a_6]; unfold cf
      push_cast
      norm_num
    have hb_7 : (a 7 : ℚ) = cf 7 := by
      rw [a_7]; unfold cf
      push_cast
      norm_num
    have hb_8 : (a 8 : ℚ) = cf 8 := by
      rw [a_8]; unfold cf
      push_cast
      norm_num
    have hb_9 : (a 9 : ℚ) = cf 9 := by
      rw [a_9]; unfold cf
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 10) = 12 * cf (m + 9) - 60 * cf (m + 8) + 162 * cf (m + 7) - 255 * cf (m + 6) + 234 * cf (m + 5) - 116 * cf (m + 4) + 24 * cf (m + 3) := by
      intro m
      unfold cf
      have hp_t_1 : (2 : ℚ) ^ (m + 4) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 1 := by
        rw [show m + 4 = (m + 3) + 1 by omega, pow_add]
      have hp_t_2 : (2 : ℚ) ^ (m + 5) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 2 := by
        rw [show m + 5 = (m + 3) + 2 by omega, pow_add]
      have hp_t_3 : (2 : ℚ) ^ (m + 6) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 3 := by
        rw [show m + 6 = (m + 3) + 3 by omega, pow_add]
      have hp_t_4 : (2 : ℚ) ^ (m + 7) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 4 := by
        rw [show m + 7 = (m + 3) + 4 by omega, pow_add]
      have hp_t_5 : (2 : ℚ) ^ (m + 8) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 5 := by
        rw [show m + 8 = (m + 3) + 5 by omega, pow_add]
      have hp_t_6 : (2 : ℚ) ^ (m + 9) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 6 := by
        rw [show m + 9 = (m + 3) + 6 by omega, pow_add]
      have hp_t_7 : (2 : ℚ) ^ (m + 10) = (2 : ℚ) ^ (m + 3) * (2 : ℚ) ^ 7 := by
        rw [show m + 10 = (m + 3) + 7 by omega, pow_add]
      have hp_c_1 : (3 : ℚ) ^ (m + 4) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 1 := by
        rw [show m + 4 = (m + 3) + 1 by omega, pow_add]
      have hp_c_2 : (3 : ℚ) ^ (m + 5) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 2 := by
        rw [show m + 5 = (m + 3) + 2 by omega, pow_add]
      have hp_c_3 : (3 : ℚ) ^ (m + 6) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 3 := by
        rw [show m + 6 = (m + 3) + 3 by omega, pow_add]
      have hp_c_4 : (3 : ℚ) ^ (m + 7) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 4 := by
        rw [show m + 7 = (m + 3) + 4 by omega, pow_add]
      have hp_c_5 : (3 : ℚ) ^ (m + 8) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 5 := by
        rw [show m + 8 = (m + 3) + 5 by omega, pow_add]
      have hp_c_6 : (3 : ℚ) ^ (m + 9) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 6 := by
        rw [show m + 9 = (m + 3) + 6 by omega, pow_add]
      have hp_c_7 : (3 : ℚ) ^ (m + 10) = (3 : ℚ) ^ (m + 3) * (3 : ℚ) ^ 7 := by
        rw [show m + 10 = (m + 3) + 7 by omega, pow_add]
      simp only [hp_t_1, hp_t_2, hp_t_3, hp_t_4, hp_t_5, hp_t_6, hp_t_7, hp_c_1, hp_c_2, hp_c_3, hp_c_4, hp_c_5, hp_c_6, hp_c_7]
      generalize (2 : ℚ) ^ (m + 3) = Xt
      generalize (3 : ℚ) ^ (m + 3) = Xc
      push_cast
      ring
    have hR : ∀ m : ℕ,
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
        simp only [Nat.zero_add]
        exact ⟨hb_3, hb_4, hb_5, hb_6, hb_7, hb_8, hb_9⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 3 = m + 4 by omega] using h1), (by simpa only [show m + 1 + 4 = m + 5 by omega] using h2), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h3), (by simpa only [show m + 1 + 6 = m + 7 by omega] using h4), (by simpa only [show m + 1 + 7 = m + 8 by omega] using h5), (by simpa only [show m + 1 + 8 = m + 9 by omega] using h6), ?_⟩
        rw [show m + 1 + 9 = m + 10 by omega]
        have hr : (a (m + 10) : ℚ) = 12 * a (m + 9) - 60 * a (m + 8) + 162 * a (m + 7) - 255 * a (m + 6) + 234 * a (m + 5) - 116 * a (m + 4) + 24 * a (m + 3) := by
          have h0' := hrec (m + 10) (by omega)
          simp only [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h6, h5, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 3)).1
    rw [show n - 3 + 3 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 3, OMA.S_oeis_a250892.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250892.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250892.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250892.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250892.main := by
  obtain ⟨hrec, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250892.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250892.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega), hA (n - 4) (by omega), hA (n - 5) (by omega), hA (n - 6) (by omega), hA (n - 7) (by omega)]
    exact hrec n (by omega)
  · rw [hser, OMA.S_oeis_a250892.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n (by omega)]; exact hcf n (by omega)

end OMA.P250892

theorem OMA.solution : type_of% @OMA.S_oeis_a250892.main := OMA.P250892.main_proof
