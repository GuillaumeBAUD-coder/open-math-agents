import OMAStatements.S_oeis_a250779

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence, g.f. and closed form bridged to upstream CellOK encoding.

namespace OMA.P250779

open PowerSeries

/-- A `2 X 2` binary subblock `(a, b / c, d)` has `a + b ≤ c + d` and `|c - a| ≤ |d - b|`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  a.val + b.val ≤ c.val + d.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 5` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 5 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 4,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 5 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250779: Number of (n+1) X (4+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250779 PowerSeries

abbrev Row := Fin 5 → Fin 2

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 4, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 32 :=
  ⟨16 * (r 0).val + 8 * (r 1).val + 4 * (r 2).val + 2 * (r 3).val + (r 4).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; omega⟩

def dec (k : Fin 32) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 16, by omega⟩
  else if c.val = 1 then ⟨(k.val / 8) % 2, by omega⟩
  else if c.val = 2 then ⟨(k.val / 4) % 2, by omega⟩
  else if c.val = 3 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 32, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega
  · change (dec (enc r) 3).val = (r 3).val; simp [dec, enc]; try omega
  · change (dec (enc r) 4).val = (r 4).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 32) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 32) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 32) : ℕ := match i.val with
  | 0 => 2147516555
  | 1 => 1073758278
  | 2 => 536879148
  | 3 => 8
  | 4 => 134219952
  | 5 => 67109984
  | 6 => 192
  | 7 => 128
  | 8 => 8424192
  | 9 => 4212224
  | 10 => 2108416
  | 11 => 2048
  | 12 => 45056
  | 13 => 24576
  | 14 => 49152
  | 15 => 32768
  | 16 => 2156625920
  | 17 => 1078345728
  | 18 => 539762688
  | 19 => 524288
  | 20 => 145754112
  | 21 => 73401344
  | 22 => 12582912
  | 23 => 8388608
  | 24 => 2332033024
  | 25 => 1174405120
  | 26 => 738197504
  | 27 => 134217728
  | 28 => 2952790016
  | 29 => 1610612736
  | 30 => 3221225472
  | 31 => 2147483648
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 32, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 32 → ℕ) (i : Fin 32) : ℕ :=
  ∑ j : Fin 32, if ok2 i j then f j else 0

def v : ℕ → Fin 32 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 32, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 32, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 32) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 32, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 32) : ℕ := match i.val with
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
  | 27 => 1
  | 28 => 1
  | 29 => 1
  | 30 => 1
  | 31 => 1
  | _ => 0

def vtab1 (i : Fin 32) : ℕ := match i.val with
  | 0 => 6
  | 1 => 5
  | 2 => 5
  | 3 => 1
  | 4 => 5
  | 5 => 4
  | 6 => 2
  | 7 => 1
  | 8 => 5
  | 9 => 4
  | 10 => 4
  | 11 => 1
  | 12 => 3
  | 13 => 2
  | 14 => 2
  | 15 => 1
  | 16 => 6
  | 17 => 5
  | 18 => 5
  | 19 => 1
  | 20 => 5
  | 21 => 4
  | 22 => 2
  | 23 => 1
  | 24 => 4
  | 25 => 3
  | 26 => 3
  | 27 => 1
  | 28 => 3
  | 29 => 2
  | 30 => 2
  | 31 => 1
  | _ => 0

def vtab2 (i : Fin 32) : ℕ := match i.val with
  | 0 => 15
  | 1 => 16
  | 2 => 14
  | 3 => 1
  | 4 => 12
  | 5 => 13
  | 6 => 3
  | 7 => 1
  | 8 => 12
  | 9 => 12
  | 10 => 11
  | 11 => 1
  | 12 => 6
  | 13 => 4
  | 14 => 3
  | 15 => 1
  | 16 => 15
  | 17 => 16
  | 18 => 14
  | 19 => 1
  | 20 => 12
  | 21 => 13
  | 22 => 3
  | 23 => 1
  | 24 => 9
  | 25 => 8
  | 26 => 6
  | 27 => 1
  | 28 => 6
  | 29 => 4
  | 30 => 3
  | 31 => 1
  | _ => 0

def vtab3 (i : Fin 32) : ℕ := match i.val with
  | 0 => 35
  | 1 => 39
  | 2 => 36
  | 3 => 1
  | 4 => 28
  | 5 => 33
  | 6 => 4
  | 7 => 1
  | 8 => 27
  | 9 => 29
  | 10 => 29
  | 11 => 1
  | 12 => 11
  | 13 => 7
  | 14 => 4
  | 15 => 1
  | 16 => 35
  | 17 => 39
  | 18 => 36
  | 19 => 1
  | 20 => 28
  | 21 => 33
  | 22 => 4
  | 23 => 1
  | 24 => 19
  | 25 => 17
  | 26 => 11
  | 27 => 1
  | 28 => 11
  | 29 => 7
  | 30 => 4
  | 31 => 1
  | _ => 0

def vtab4 (i : Fin 32) : ℕ := match i.val with
  | 0 => 78
  | 1 => 87
  | 2 => 84
  | 3 => 1
  | 4 => 64
  | 5 => 77
  | 6 => 5
  | 7 => 1
  | 8 => 59
  | 9 => 66
  | 10 => 70
  | 11 => 1
  | 12 => 19
  | 13 => 11
  | 14 => 5
  | 15 => 1
  | 16 => 78
  | 17 => 87
  | 18 => 84
  | 19 => 1
  | 20 => 64
  | 21 => 77
  | 22 => 5
  | 23 => 1
  | 24 => 38
  | 25 => 32
  | 26 => 19
  | 27 => 1
  | 28 => 19
  | 29 => 11
  | 30 => 5
  | 31 => 1
  | _ => 0

def vtab5 (i : Fin 32) : ℕ := match i.val with
  | 0 => 169
  | 1 => 186
  | 2 => 184
  | 3 => 1
  | 4 => 144
  | 5 => 171
  | 6 => 6
  | 7 => 1
  | 8 => 128
  | 9 => 146
  | 10 => 159
  | 11 => 1
  | 12 => 31
  | 13 => 16
  | 14 => 6
  | 15 => 1
  | 16 => 169
  | 17 => 186
  | 18 => 184
  | 19 => 1
  | 20 => 144
  | 21 => 171
  | 22 => 6
  | 23 => 1
  | 24 => 72
  | 25 => 56
  | 26 => 31
  | 27 => 1
  | 28 => 31
  | 29 => 16
  | 30 => 6
  | 31 => 1
  | _ => 0

def vtab6 (i : Fin 32) : ℕ := match i.val with
  | 0 => 359
  | 1 => 388
  | 2 => 388
  | 3 => 1
  | 4 => 318
  | 5 => 367
  | 6 => 7
  | 7 => 1
  | 8 => 277
  | 9 => 317
  | 10 => 347
  | 11 => 1
  | 12 => 48
  | 13 => 22
  | 14 => 7
  | 15 => 1
  | 16 => 359
  | 17 => 388
  | 18 => 388
  | 19 => 1
  | 20 => 318
  | 21 => 367
  | 22 => 7
  | 23 => 1
  | 24 => 130
  | 25 => 93
  | 26 => 48
  | 27 => 1
  | 28 => 48
  | 29 => 22
  | 30 => 7
  | 31 => 1
  | _ => 0

def vtab7 (i : Fin 32) : ℕ := match i.val with
  | 0 => 751
  | 1 => 797
  | 2 => 800
  | 3 => 1
  | 4 => 688
  | 5 => 769
  | 6 => 8
  | 7 => 1
  | 8 => 597
  | 9 => 678
  | 10 => 737
  | 11 => 1
  | 12 => 71
  | 13 => 29
  | 14 => 8
  | 15 => 1
  | 16 => 751
  | 17 => 797
  | 18 => 800
  | 19 => 1
  | 20 => 688
  | 21 => 769
  | 22 => 8
  | 23 => 1
  | 24 => 225
  | 25 => 148
  | 26 => 71
  | 27 => 1
  | 28 => 71
  | 29 => 29
  | 30 => 8
  | 31 => 1
  | _ => 0

def vtab8 (i : Fin 32) : ℕ := match i.val with
  | 0 => 1552
  | 1 => 1621
  | 2 => 1628
  | 3 => 1
  | 4 => 1460
  | 5 => 1585
  | 6 => 9
  | 7 => 1
  | 8 => 1278
  | 9 => 1431
  | 10 => 1536
  | 11 => 1
  | 12 => 101
  | 13 => 37
  | 14 => 9
  | 15 => 1
  | 16 => 1552
  | 17 => 1621
  | 18 => 1628
  | 19 => 1
  | 20 => 1460
  | 21 => 1585
  | 22 => 9
  | 23 => 1
  | 24 => 375
  | 25 => 227
  | 26 => 101
  | 27 => 1
  | 28 => 101
  | 29 => 37
  | 30 => 9
  | 31 => 1
  | _ => 0

def vtab9 (i : Fin 32) : ℕ := match i.val with
  | 0 => 3177
  | 1 => 3276
  | 2 => 3288
  | 3 => 1
  | 4 => 3048
  | 5 => 3231
  | 6 => 10
  | 7 => 1
  | 8 => 2712
  | 9 => 2985
  | 10 => 3159
  | 11 => 1
  | 12 => 139
  | 13 => 46
  | 14 => 10
  | 15 => 1
  | 16 => 3177
  | 17 => 3276
  | 18 => 3288
  | 19 => 1
  | 20 => 3048
  | 21 => 3231
  | 22 => 10
  | 23 => 1
  | 24 => 604
  | 25 => 337
  | 26 => 139
  | 27 => 1
  | 28 => 139
  | 29 => 46
  | 30 => 10
  | 31 => 1
  | _ => 0

def vtab10 (i : Fin 32) : ℕ := match i.val with
  | 0 => 6457
  | 1 => 6594
  | 2 => 6612
  | 3 => 1
  | 4 => 6282
  | 5 => 6539
  | 6 => 11
  | 7 => 1
  | 8 => 5700
  | 9 => 6164
  | 10 => 6437
  | 11 => 1
  | 12 => 186
  | 13 => 56
  | 14 => 11
  | 15 => 1
  | 16 => 6457
  | 17 => 6594
  | 18 => 6612
  | 19 => 1
  | 20 => 6282
  | 21 => 6539
  | 22 => 11
  | 23 => 1
  | 24 => 943
  | 25 => 486
  | 26 => 186
  | 27 => 1
  | 28 => 186
  | 29 => 56
  | 30 => 11
  | 31 => 1
  | _ => 0

def vtab11 (i : Fin 32) : ℕ := match i.val with
  | 0 => 13055
  | 1 => 13239
  | 2 => 13264
  | 3 => 1
  | 4 => 12824
  | 5 => 13173
  | 6 => 12
  | 7 => 1
  | 8 => 11867
  | 9 => 12623
  | 10 => 13033
  | 11 => 1
  | 12 => 243
  | 13 => 67
  | 14 => 12
  | 15 => 1
  | 16 => 13055
  | 17 => 13239
  | 18 => 13264
  | 19 => 1
  | 20 => 12824
  | 21 => 13173
  | 22 => 12
  | 23 => 1
  | 24 => 1431
  | 25 => 683
  | 26 => 243
  | 27 => 1
  | 28 => 243
  | 29 => 67
  | 30 => 12
  | 31 => 1
  | _ => 0

def vtab12 (i : Fin 32) : ℕ := match i.val with
  | 0 => 26298
  | 1 => 26539
  | 2 => 26572
  | 3 => 1
  | 4 => 26000
  | 5 => 26461
  | 6 => 13
  | 7 => 1
  | 8 => 24493
  | 9 => 25680
  | 10 => 26274
  | 11 => 1
  | 12 => 311
  | 13 => 79
  | 14 => 13
  | 15 => 1
  | 16 => 26298
  | 17 => 26539
  | 18 => 26572
  | 19 => 1
  | 20 => 26000
  | 21 => 26461
  | 22 => 13
  | 23 => 1
  | 24 => 2116
  | 25 => 938
  | 26 => 311
  | 27 => 1
  | 28 => 311
  | 29 => 79
  | 30 => 13
  | 31 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 32, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 32, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 32, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 32, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 32, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 32, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel
lemma v_6 : ∀ i : Fin 32, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel
lemma v_7 : ∀ i : Fin 32, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 32, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel
lemma v_9 : ∀ i : Fin 32, v 9 i = vtab9 i := by
  intro i; rw [show (9 : ℕ) = 8 + 1 from rfl, v, step]; simp only [v_8, ok2_iff]; revert i; decide +kernel
lemma v_10 : ∀ i : Fin 32, v 10 i = vtab10 i := by
  intro i; rw [show (10 : ℕ) = 9 + 1 from rfl, v, step]; simp only [v_9, ok2_iff]; revert i; decide +kernel
lemma v_11 : ∀ i : Fin 32, v 11 i = vtab11 i := by
  intro i; rw [show (11 : ℕ) = 10 + 1 from rfl, v, step]; simp only [v_10, ok2_iff]; revert i; decide +kernel
lemma v_12 : ∀ i : Fin 32, v 12 i = vtab12 i := by
  intro i; rw [show (12 : ℕ) = 11 + 1 from rfl, v, step]; simp only [v_11, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 32) : ℤ :=
  (v (m + 7) i : ℤ) - 8 * (v (m + 6) i : ℤ) + 27 * (v (m + 5) i : ℤ) - 50 * (v (m + 4) i : ℤ) + 55 * (v (m + 3) i : ℤ) - 36 * (v (m + 2) i : ℤ) + 13 * (v (m + 1) i : ℤ) - 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 32, err 1 i = 0 := by
  intro i
  change (v 8 i : ℤ) - 8 * (v 7 i : ℤ) + 27 * (v 6 i : ℤ) - 50 * (v 5 i : ℤ) + 55 * (v 4 i : ℤ) - 36 * (v 3 i : ℤ) + 13 * (v 2 i : ℤ) - 2 * (v 1 i : ℤ) = 0
  simp only [v_8, v_7, v_6, v_5, v_4, v_3, v_2, v_1]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 32) :
    err (m + 1) i = ∑ j : Fin 32, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 32, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 32) : err (m + 1) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_m (m : ℕ) :
    (a (m + 8) : ℤ) = 8 * a (m + 7) - 27 * a (m + 6) + 50 * a (m + 5) - 55 * a (m + 4) + 36 * a (m + 3) - 13 * a (m + 2) + 2 * a (m + 1) := by
  have h : ∑ i : Fin 32, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 32, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 32, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  have h2_5 : m + 1 + 5 = m + 6 := by omega
  have h2_6 : m + 1 + 6 = m + 7 := by omega
  have h2_7 : m + 1 + 7 = m + 8 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 99 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 1 i = 99
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 238 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 2 i = 238
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 534 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 3 i = 534
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 1152 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 4 i = 1152
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 2426 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 5 i = 2426
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 5028 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 6 i = 5028
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 10306 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 7 i = 10306
  simp only [v_7]; decide +kernel
lemma a_8 : a 8 = 20960 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 8 i = 20960
  simp only [v_8]; decide +kernel
lemma a_9 : a 9 = 42394 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 9 i = 42394
  simp only [v_9]; decide +kernel
lemma a_10 : a 10 = 85420 := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 10 i = 85420
  simp only [v_10]; decide +kernel
lemma a_11 : a 11 = 171666 := by
  rw [show (11 : ℕ) = 10 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 11 i = 171666
  simp only [v_11]; decide +kernel
lemma a_12 : a 12 = 344392 := by
  rw [show (12 : ℕ) = 11 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 12 i = 344392
  simp only [v_12]; decide +kernel

def e (m : ℕ) : ℤ := (a (m + 6) : ℤ) - (6 * a (m + 5) - 14 * a (m + 4) + 16 * a (m + 3) - 9 * a (m + 2) + 2 * a (m + 1))

lemma e_rec (m : ℕ) : e (m + 7) = 8 * e (m + 6) - 27 * e (m + 5) + 50 * e (m + 4) - 55 * e (m + 3) + 36 * e (m + 2) - 13 * e (m + 1) + 2 * e m := by
  have g0 : (a (m + 13) : ℤ) = 8 * a (m + 12) - 27 * a (m + 11) + 50 * a (m + 10) - 55 * a (m + 9) + 36 * a (m + 8) - 13 * a (m + 7) + 2 * a (m + 6) := by
    have h := a_rec_m (m + 5)
    simp only [show m + 5 + 8 = m + 13 by omega, show m + 5 + 7 = m + 12 by omega, show m + 5 + 6 = m + 11 by omega, show m + 5 + 5 = m + 10 by omega, show m + 5 + 4 = m + 9 by omega, show m + 5 + 3 = m + 8 by omega, show m + 5 + 2 = m + 7 by omega, show m + 5 + 1 = m + 6 by omega] at h
    exact h
  have g1 : (a (m + 12) : ℤ) = 8 * a (m + 11) - 27 * a (m + 10) + 50 * a (m + 9) - 55 * a (m + 8) + 36 * a (m + 7) - 13 * a (m + 6) + 2 * a (m + 5) := by
    have h := a_rec_m (m + 4)
    simp only [show m + 4 + 8 = m + 12 by omega, show m + 4 + 7 = m + 11 by omega, show m + 4 + 6 = m + 10 by omega, show m + 4 + 5 = m + 9 by omega, show m + 4 + 4 = m + 8 by omega, show m + 4 + 3 = m + 7 by omega, show m + 4 + 2 = m + 6 by omega, show m + 4 + 1 = m + 5 by omega] at h
    exact h
  have g2 : (a (m + 11) : ℤ) = 8 * a (m + 10) - 27 * a (m + 9) + 50 * a (m + 8) - 55 * a (m + 7) + 36 * a (m + 6) - 13 * a (m + 5) + 2 * a (m + 4) := by
    have h := a_rec_m (m + 3)
    simp only [show m + 3 + 8 = m + 11 by omega, show m + 3 + 7 = m + 10 by omega, show m + 3 + 6 = m + 9 by omega, show m + 3 + 5 = m + 8 by omega, show m + 3 + 4 = m + 7 by omega, show m + 3 + 3 = m + 6 by omega, show m + 3 + 2 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega] at h
    exact h
  have g3 : (a (m + 10) : ℤ) = 8 * a (m + 9) - 27 * a (m + 8) + 50 * a (m + 7) - 55 * a (m + 6) + 36 * a (m + 5) - 13 * a (m + 4) + 2 * a (m + 3) := by
    have h := a_rec_m (m + 2)
    simp only [show m + 2 + 8 = m + 10 by omega, show m + 2 + 7 = m + 9 by omega, show m + 2 + 6 = m + 8 by omega, show m + 2 + 5 = m + 7 by omega, show m + 2 + 4 = m + 6 by omega, show m + 2 + 3 = m + 5 by omega, show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at h
    exact h
  have g4 : (a (m + 9) : ℤ) = 8 * a (m + 8) - 27 * a (m + 7) + 50 * a (m + 6) - 55 * a (m + 5) + 36 * a (m + 4) - 13 * a (m + 3) + 2 * a (m + 2) := by
    have h := a_rec_m (m + 1)
    simp only [show m + 1 + 8 = m + 9 by omega, show m + 1 + 7 = m + 8 by omega, show m + 1 + 6 = m + 7 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h
    exact h
  have g5 : (a (m + 8) : ℤ) = 8 * a (m + 7) - 27 * a (m + 6) + 50 * a (m + 5) - 55 * a (m + 4) + 36 * a (m + 3) - 13 * a (m + 2) + 2 * a (m + 1) := by
    have h := a_rec_m (m + 0)
    simp only [show m + 0 + 8 = m + 8 by omega, show m + 0 + 7 = m + 7 by omega, show m + 0 + 6 = m + 6 by omega, show m + 0 + 5 = m + 5 by omega, show m + 0 + 4 = m + 4 by omega, show m + 0 + 3 = m + 3 by omega, show m + 0 + 2 = m + 2 by omega, show m + 0 + 1 = m + 1 by omega] at h
    exact h
  simp only [e, show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 6 = m + 7 by omega, show m + 2 + 1 = m + 3 by omega, show m + 2 + 2 = m + 4 by omega, show m + 2 + 3 = m + 5 by omega, show m + 2 + 4 = m + 6 by omega, show m + 2 + 5 = m + 7 by omega, show m + 2 + 6 = m + 8 by omega, show m + 3 + 1 = m + 4 by omega, show m + 3 + 2 = m + 5 by omega, show m + 3 + 3 = m + 6 by omega, show m + 3 + 4 = m + 7 by omega, show m + 3 + 5 = m + 8 by omega, show m + 3 + 6 = m + 9 by omega, show m + 4 + 1 = m + 5 by omega, show m + 4 + 2 = m + 6 by omega, show m + 4 + 3 = m + 7 by omega, show m + 4 + 4 = m + 8 by omega, show m + 4 + 5 = m + 9 by omega, show m + 4 + 6 = m + 10 by omega, show m + 5 + 1 = m + 6 by omega, show m + 5 + 2 = m + 7 by omega, show m + 5 + 3 = m + 8 by omega, show m + 5 + 4 = m + 9 by omega, show m + 5 + 5 = m + 10 by omega, show m + 5 + 6 = m + 11 by omega, show m + 6 + 1 = m + 7 by omega, show m + 6 + 2 = m + 8 by omega, show m + 6 + 3 = m + 9 by omega, show m + 6 + 4 = m + 10 by omega, show m + 6 + 5 = m + 11 by omega, show m + 6 + 6 = m + 12 by omega, show m + 7 + 1 = m + 8 by omega, show m + 7 + 2 = m + 9 by omega, show m + 7 + 3 = m + 10 by omega, show m + 7 + 4 = m + 11 by omega, show m + 7 + 5 = m + 12 by omega, show m + 7 + 6 = m + 13 by omega]
  linear_combination (1) * g0 + (-6) * g1 + (14) * g2 + (-16) * g3 + (9) * g4 + (-2) * g5

lemma e_zero : ∀ m : ℕ, e m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 7 with h | h
    · interval_cases m <;> norm_num [e, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12]
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 7 := ⟨m - 7, by omega⟩
      rw [e_rec t]
      simp [ih (t + 6) (by omega), ih (t + 5) (by omega), ih (t + 4) (by omega), ih (t + 3) (by omega), ih (t + 2) (by omega), ih (t + 1) (by omega), ih t (by omega)]

lemma a_rec_ge (m : ℕ) :
    (a (m + 6) : ℤ) = 6 * a (m + 5) - 14 * a (m + 4) + 16 * a (m + 3) - 9 * a (m + 2) + 2 * a (m + 1) := by
  have h := e_zero m
  unfold e at h
  linarith

def cf (n : ℕ) : ℚ :=
  (-288 + 507 * (2 : ℚ) ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6


theorem main_proof_ours :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) + 2 * a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 - 2 * X)) =
      X * (99 - 356 * X + 492 * X ^ 2 - 304 * X ^ 3 + 73 * X ^ 4)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-288 + 507 * (2 : ℚ) ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6) := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) + 2 * a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 - 2 * X)) =
      X * (99 - 356 * X + 492 * X ^ 2 - 304 * X ^ 3 + 73 * X ^ 4) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 - 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (14 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (16 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (9 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (99 - 356 * X + 492 * X ^ 2 - 304 * X ^ 3 + 73 * X ^ 4) : PowerSeries ℚ) =
        C (99 : ℚ) * X ^ 1 - C (356 : ℚ) * X ^ 2 + C (492 : ℚ) * X ^ 3 - C (304 : ℚ) * X ^ 4 + C (73 : ℚ) * X ^ 5 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12] <;> try norm_num
    · have hq : (a n : ℚ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) - 9 * a (n - 4) + 2 * a (n - 5) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have c5 : 5 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, c5, e1, e2, e3, e4, e5, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-288 + 507 * (2 : ℚ) ^ n - 116 * (n : ℚ) - 12 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) / 6 := by
    have hb_1 : (a 1 : ℚ) = cf 1 := by
      rw [a_1]; unfold cf
      push_cast
      norm_num
    have hb_2 : (a 2 : ℚ) = cf 2 := by
      rw [a_2]; unfold cf
      push_cast
      norm_num
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
    have cf_rec : ∀ m : ℕ, cf (m + 6) = 6 * cf (m + 5) - 14 * cf (m + 4) + 16 * cf (m + 3) - 9 * cf (m + 2) + 2 * cf (m + 1) := by
      intro m
      unfold cf
      have hp_t_1 : (2 : ℚ) ^ (m + 2) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_t_2 : (2 : ℚ) ^ (m + 3) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_t_3 : (2 : ℚ) ^ (m + 4) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_t_4 : (2 : ℚ) ^ (m + 5) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 4 := by
        rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      have hp_t_5 : (2 : ℚ) ^ (m + 6) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 5 := by
        rw [show m + 6 = (m + 1) + 5 by omega, pow_add]
      simp only [hp_t_1, hp_t_2, hp_t_3, hp_t_4, hp_t_5]
      generalize (2 : ℚ) ^ (m + 1) = Xt
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 1) : ℚ) = cf (m + 1) ∧
        (a (m + 2) : ℚ) = cf (m + 2) ∧
        (a (m + 3) : ℚ) = cf (m + 3) ∧
        (a (m + 4) : ℚ) = cf (m + 4) ∧
        (a (m + 5) : ℚ) = cf (m + 5) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_1, hb_2, hb_3, hb_4, hb_5⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), (by simpa only [show m + 1 + 3 = m + 4 by omega] using h3), (by simpa only [show m + 1 + 4 = m + 5 by omega] using h4), ?_⟩
        rw [show m + 1 + 5 = m + 6 by omega]
        have hr : (a (m + 6) : ℚ) = 6 * a (m + 5) - 14 * a (m + 4) + 16 * a (m + 3) - 9 * a (m + 2) + 2 * a (m + 1) := by
          have h0' := hrec (m + 6) (by omega)
          simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 2,
    OMA.S_oeis_a250779.CellOK ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) ((r : ℕ) : ℤ) ((s : ℕ) : ℤ) ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250779.CellOK, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250779.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250779.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250779.main := by
  obtain ⟨hrec, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250779.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250779.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega), hA (n - 4) (by omega), hA (n - 5) (by omega)]
    exact hrec n (by omega)
  · rw [hser, OMA.S_oeis_a250779.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n (by omega)]
    exact hcf n (by omega)

end OMA.P250779

theorem OMA.solution : type_of% @OMA.S_oeis_a250779.main := OMA.P250779.main_proof
