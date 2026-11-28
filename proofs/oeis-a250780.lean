import OMAStatements.S_oeis_a250780

-- Credit: @Dariusthedoggie
-- Proof: row transfer matrix annihilated by the order-7 recurrence polynomial, giving recurrence, g.f. and closed form, bridged to the Nat.card encoding.

namespace OMA.P250780

open PowerSeries
/-- A `2 X 2` binary subblock `(a, b / c, d)` has `a + b ≤ c + d` and `|c - a| ≤ |d - b|`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  a.val + b.val ≤ c.val + d.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 6` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 6 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 5,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 6 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250780: Number of (n+1) X (5+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 6 → Fin 2

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 5, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 64 :=
  ⟨32 * (r 0).val + 16 * (r 1).val + 8 * (r 2).val + 4 * (r 3).val + 2 * (r 4).val + (r 5).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt; omega⟩

def dec (k : Fin 64) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 32, by omega⟩
  else if c.val = 1 then ⟨(k.val / 16) % 2, by omega⟩
  else if c.val = 2 then ⟨(k.val / 8) % 2, by omega⟩
  else if c.val = 3 then ⟨(k.val / 4) % 2, by omega⟩
  else if c.val = 4 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 64, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; have h4 := (r 4).isLt; have h5 := (r 5).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega
  · change (dec (enc r) 3).val = (r 3).val; simp [dec, enc]; try omega
  · change (dec (enc r) 4).val = (r 4).val; simp [dec, enc]; try omega
  · change (dec (enc r) 5).val = (r 5).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 64) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 64) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 64) : ℕ := match i.val with
  | 0 => 9223372039002292363
  | 1 => 4611686019501146182
  | 2 => 2305843009750573100
  | 3 => 8
  | 4 => 576460752437643440
  | 5 => 288230376218821728
  | 6 => 192
  | 7 => 128
  | 8 => 36028797027388160
  | 9 => 18014398513694208
  | 10 => 9007199256849408
  | 11 => 2048
  | 12 => 45056
  | 13 => 24576
  | 14 => 49152
  | 15 => 32768
  | 16 => 140739644948480
  | 17 => 70369822507008
  | 18 => 35184911843328
  | 19 => 524288
  | 20 => 8796238774272
  | 21 => 4398119911424
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
  | 32 => 9223513373491068928
  | 33 => 4611756688893018112
  | 34 => 2305878383101214720
  | 35 => 34359738368
  | 36 => 576470304444907520
  | 37 => 288235186582192128
  | 38 => 824633720832
  | 39 => 549755813888
  | 40 => 36181629143613440
  | 41 => 18091364327620608
  | 42 => 9055577768460288
  | 43 => 8796093022208
  | 44 => 193514046488576
  | 45 => 105553116266496
  | 46 => 211106232532992
  | 47 => 140737488355328
  | 48 => 9262497058617556992
  | 49 => 4631389266797133824
  | 50 => 2318227908188962816
  | 51 => 2251799813685248
  | 52 => 626000348204498944
  | 53 => 315251973915934720
  | 54 => 54043195528445952
  | 55 => 36028797018963968
  | 56 => 10016005571271983104
  | 57 => 5044031582654955520
  | 58 => 3170534137668829184
  | 59 => 576460752303423488
  | 60 => 12682136550675316736
  | 61 => 6917529027641081856
  | 62 => 13835058055282163712
  | 63 => 9223372036854775808
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 64, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 64 → ℕ) (i : Fin 64) : ℕ :=
  ∑ j : Fin 64, if ok2 i j then f j else 0

def v : ℕ → Fin 64 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 64, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 64, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 64) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 64, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 64) : ℕ := match i.val with
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
  | 32 => 1
  | 33 => 1
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 1
  | 38 => 1
  | 39 => 1
  | 40 => 1
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 1
  | 51 => 1
  | 52 => 1
  | 53 => 1
  | 54 => 1
  | 55 => 1
  | 56 => 1
  | 57 => 1
  | 58 => 1
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 1
  | 63 => 1
  | _ => 0

def vtab1 (i : Fin 64) : ℕ := match i.val with
  | 0 => 7
  | 1 => 6
  | 2 => 6
  | 3 => 1
  | 4 => 6
  | 5 => 5
  | 6 => 2
  | 7 => 1
  | 8 => 6
  | 9 => 5
  | 10 => 5
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
  | 32 => 7
  | 33 => 6
  | 34 => 6
  | 35 => 1
  | 36 => 6
  | 37 => 5
  | 38 => 2
  | 39 => 1
  | 40 => 6
  | 41 => 5
  | 42 => 5
  | 43 => 1
  | 44 => 3
  | 45 => 2
  | 46 => 2
  | 47 => 1
  | 48 => 5
  | 49 => 4
  | 50 => 4
  | 51 => 1
  | 52 => 4
  | 53 => 3
  | 54 => 2
  | 55 => 1
  | 56 => 4
  | 57 => 3
  | 58 => 3
  | 59 => 1
  | 60 => 3
  | 61 => 2
  | 62 => 2
  | 63 => 1
  | _ => 0

def vtab2 (i : Fin 64) : ℕ := match i.val with
  | 0 => 18
  | 1 => 20
  | 2 => 18
  | 3 => 1
  | 4 => 15
  | 5 => 18
  | 6 => 3
  | 7 => 1
  | 8 => 15
  | 9 => 16
  | 10 => 15
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
  | 21 => 14
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
  | 32 => 18
  | 33 => 20
  | 34 => 18
  | 35 => 1
  | 36 => 15
  | 37 => 18
  | 38 => 3
  | 39 => 1
  | 40 => 15
  | 41 => 16
  | 42 => 15
  | 43 => 1
  | 44 => 6
  | 45 => 4
  | 46 => 3
  | 47 => 1
  | 48 => 12
  | 49 => 12
  | 50 => 10
  | 51 => 1
  | 52 => 9
  | 53 => 8
  | 54 => 3
  | 55 => 1
  | 56 => 9
  | 57 => 8
  | 58 => 6
  | 59 => 1
  | 60 => 6
  | 61 => 4
  | 62 => 3
  | 63 => 1
  | _ => 0

def vtab3 (i : Fin 64) : ℕ := match i.val with
  | 0 => 43
  | 1 => 50
  | 2 => 49
  | 3 => 1
  | 4 => 37
  | 5 => 48
  | 6 => 4
  | 7 => 1
  | 8 => 35
  | 9 => 40
  | 10 => 42
  | 11 => 1
  | 12 => 11
  | 13 => 7
  | 14 => 4
  | 15 => 1
  | 16 => 35
  | 17 => 39
  | 18 => 37
  | 19 => 1
  | 20 => 29
  | 21 => 38
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
  | 32 => 43
  | 33 => 50
  | 34 => 49
  | 35 => 1
  | 36 => 37
  | 37 => 48
  | 38 => 4
  | 39 => 1
  | 40 => 35
  | 41 => 40
  | 42 => 42
  | 43 => 1
  | 44 => 11
  | 45 => 7
  | 46 => 4
  | 47 => 1
  | 48 => 27
  | 49 => 28
  | 50 => 23
  | 51 => 1
  | 52 => 19
  | 53 => 17
  | 54 => 4
  | 55 => 1
  | 56 => 19
  | 57 => 17
  | 58 => 11
  | 59 => 1
  | 60 => 11
  | 61 => 7
  | 62 => 4
  | 63 => 1
  | _ => 0

def vtab4 (i : Fin 64) : ℕ := match i.val with
  | 0 => 98
  | 1 => 115
  | 2 => 119
  | 3 => 1
  | 4 => 89
  | 5 => 116
  | 6 => 5
  | 7 => 1
  | 8 => 79
  | 9 => 94
  | 10 => 105
  | 11 => 1
  | 12 => 19
  | 13 => 11
  | 14 => 5
  | 15 => 1
  | 16 => 78
  | 17 => 88
  | 18 => 90
  | 19 => 1
  | 20 => 70
  | 21 => 95
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
  | 32 => 98
  | 33 => 115
  | 34 => 119
  | 35 => 1
  | 36 => 89
  | 37 => 116
  | 38 => 5
  | 39 => 1
  | 40 => 79
  | 41 => 94
  | 42 => 105
  | 43 => 1
  | 44 => 19
  | 45 => 11
  | 46 => 5
  | 47 => 1
  | 48 => 58
  | 49 => 59
  | 50 => 48
  | 51 => 1
  | 52 => 38
  | 53 => 32
  | 54 => 5
  | 55 => 1
  | 56 => 38
  | 57 => 32
  | 58 => 19
  | 59 => 1
  | 60 => 19
  | 61 => 11
  | 62 => 5
  | 63 => 1
  | _ => 0

def vtab5 (i : Fin 64) : ℕ := match i.val with
  | 0 => 218
  | 1 => 254
  | 2 => 269
  | 3 => 1
  | 4 => 209
  | 5 => 264
  | 6 => 6
  | 7 => 1
  | 8 => 177
  | 9 => 214
  | 10 => 244
  | 11 => 1
  | 12 => 31
  | 13 => 16
  | 14 => 6
  | 15 => 1
  | 16 => 170
  | 17 => 193
  | 18 => 208
  | 19 => 1
  | 20 => 168
  | 21 => 224
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
  | 32 => 218
  | 33 => 254
  | 34 => 269
  | 35 => 1
  | 36 => 209
  | 37 => 264
  | 38 => 6
  | 39 => 1
  | 40 => 177
  | 41 => 214
  | 42 => 244
  | 43 => 1
  | 44 => 31
  | 45 => 16
  | 46 => 6
  | 47 => 1
  | 48 => 120
  | 49 => 117
  | 50 => 92
  | 51 => 1
  | 52 => 72
  | 53 => 56
  | 54 => 6
  | 55 => 1
  | 56 => 72
  | 57 => 56
  | 58 => 31
  | 59 => 1
  | 60 => 31
  | 61 => 16
  | 62 => 6
  | 63 => 1
  | _ => 0

def vtab6 (i : Fin 64) : ℕ := match i.val with
  | 0 => 477
  | 1 => 547
  | 2 => 582
  | 3 => 1
  | 4 => 477
  | 5 => 576
  | 6 => 7
  | 7 => 1
  | 8 => 395
  | 9 => 476
  | 10 => 541
  | 11 => 1
  | 12 => 48
  | 13 => 22
  | 14 => 7
  | 15 => 1
  | 16 => 367
  | 17 => 419
  | 18 => 465
  | 19 => 1
  | 20 => 395
  | 21 => 505
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
  | 32 => 477
  | 33 => 547
  | 34 => 582
  | 35 => 1
  | 36 => 477
  | 37 => 576
  | 38 => 7
  | 39 => 1
  | 40 => 395
  | 41 => 476
  | 42 => 541
  | 43 => 1
  | 44 => 48
  | 45 => 22
  | 46 => 7
  | 47 => 1
  | 48 => 240
  | 49 => 221
  | 50 => 165
  | 51 => 1
  | 52 => 130
  | 53 => 93
  | 54 => 7
  | 55 => 1
  | 56 => 130
  | 57 => 93
  | 58 => 48
  | 59 => 1
  | 60 => 48
  | 61 => 22
  | 62 => 7
  | 63 => 1
  | _ => 0

def vtab7 (i : Fin 64) : ℕ := match i.val with
  | 0 => 1029
  | 1 => 1157
  | 2 => 1225
  | 3 => 1
  | 4 => 1057
  | 5 => 1220
  | 6 => 8
  | 7 => 1
  | 8 => 875
  | 9 => 1038
  | 10 => 1162
  | 11 => 1
  | 12 => 71
  | 13 => 29
  | 14 => 8
  | 15 => 1
  | 16 => 790
  | 17 => 905
  | 18 => 1015
  | 19 => 1
  | 20 => 903
  | 21 => 1101
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
  | 32 => 1029
  | 33 => 1157
  | 34 => 1225
  | 35 => 1
  | 36 => 1057
  | 37 => 1220
  | 38 => 8
  | 39 => 1
  | 40 => 875
  | 41 => 1038
  | 42 => 1162
  | 43 => 1
  | 44 => 71
  | 45 => 29
  | 46 => 8
  | 47 => 1
  | 48 => 464
  | 49 => 400
  | 50 => 281
  | 51 => 1
  | 52 => 225
  | 53 => 148
  | 54 => 8
  | 55 => 1
  | 56 => 225
  | 57 => 148
  | 58 => 71
  | 59 => 1
  | 60 => 71
  | 61 => 29
  | 62 => 8
  | 63 => 1
  | _ => 0

def vtab8 (i : Fin 64) : ℕ := match i.val with
  | 0 => 2191
  | 1 => 2414
  | 2 => 2533
  | 3 => 1
  | 4 => 2281
  | 5 => 2532
  | 6 => 9
  | 7 => 1
  | 8 => 1917
  | 9 => 2224
  | 10 => 2441
  | 11 => 1
  | 12 => 101
  | 13 => 37
  | 14 => 9
  | 15 => 1
  | 16 => 1699
  | 17 => 1944
  | 18 => 2175
  | 19 => 1
  | 20 => 2007
  | 21 => 2342
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
  | 32 => 2191
  | 33 => 2414
  | 34 => 2533
  | 35 => 1
  | 36 => 2281
  | 37 => 2532
  | 38 => 9
  | 39 => 1
  | 40 => 1917
  | 41 => 2224
  | 42 => 2441
  | 43 => 1
  | 44 => 101
  | 45 => 37
  | 46 => 9
  | 47 => 1
  | 48 => 867
  | 49 => 697
  | 50 => 459
  | 51 => 1
  | 52 => 375
  | 53 => 227
  | 54 => 9
  | 55 => 1
  | 56 => 375
  | 57 => 227
  | 58 => 101
  | 59 => 1
  | 60 => 101
  | 61 => 37
  | 62 => 9
  | 63 => 1
  | _ => 0

def vtab9 (i : Fin 64) : ℕ := match i.val with
  | 0 => 4610
  | 1 => 4983
  | 2 => 5177
  | 3 => 1
  | 4 => 4817
  | 5 => 5184
  | 6 => 10
  | 7 => 1
  | 8 => 4145
  | 9 => 4692
  | 10 => 5048
  | 11 => 1
  | 12 => 139
  | 13 => 46
  | 14 => 10
  | 15 => 1
  | 16 => 3647
  | 17 => 4146
  | 18 => 4592
  | 19 => 1
  | 20 => 4352
  | 21 => 4893
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
  | 32 => 4610
  | 33 => 4983
  | 34 => 5177
  | 35 => 1
  | 36 => 4817
  | 37 => 5184
  | 38 => 10
  | 39 => 1
  | 40 => 4145
  | 41 => 4692
  | 42 => 5048
  | 43 => 1
  | 44 => 139
  | 45 => 46
  | 46 => 10
  | 47 => 1
  | 48 => 1567
  | 49 => 1174
  | 50 => 724
  | 51 => 1
  | 52 => 604
  | 53 => 337
  | 54 => 10
  | 55 => 1
  | 56 => 604
  | 57 => 337
  | 58 => 139
  | 59 => 1
  | 60 => 139
  | 61 => 46
  | 62 => 10
  | 63 => 1
  | _ => 0

def vtab10 (i : Fin 64) : ℕ := match i.val with
  | 0 => 9598
  | 1 => 10200
  | 2 => 10500
  | 3 => 1
  | 4 => 10005
  | 5 => 10520
  | 6 => 11
  | 7 => 1
  | 8 => 8841
  | 9 => 9770
  | 10 => 10325
  | 11 => 1
  | 12 => 186
  | 13 => 56
  | 14 => 11
  | 15 => 1
  | 16 => 7797
  | 17 => 8768
  | 18 => 9578
  | 19 => 1
  | 20 => 9248
  | 21 => 10090
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
  | 32 => 9598
  | 33 => 10200
  | 34 => 10500
  | 35 => 1
  | 36 => 10005
  | 37 => 10520
  | 38 => 11
  | 39 => 1
  | 40 => 8841
  | 41 => 9770
  | 42 => 10325
  | 43 => 1
  | 44 => 186
  | 45 => 56
  | 46 => 11
  | 47 => 1
  | 48 => 2744
  | 49 => 1918
  | 50 => 1108
  | 51 => 1
  | 52 => 943
  | 53 => 486
  | 54 => 11
  | 55 => 1
  | 56 => 943
  | 57 => 486
  | 58 => 186
  | 59 => 1
  | 60 => 186
  | 61 => 56
  | 62 => 11
  | 63 => 1
  | _ => 0

def vtab11 (i : Fin 64) : ℕ := match i.val with
  | 0 => 19803
  | 1 => 20744
  | 2 => 21189
  | 3 => 1
  | 4 => 20529
  | 5 => 21228
  | 6 => 12
  | 7 => 1
  | 8 => 18615
  | 9 => 20128
  | 10 => 20958
  | 11 => 1
  | 12 => 243
  | 13 => 67
  | 14 => 12
  | 15 => 1
  | 16 => 16569
  | 17 => 18379
  | 18 => 19781
  | 19 => 1
  | 20 => 19341
  | 21 => 20612
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
  | 32 => 19803
  | 33 => 20744
  | 34 => 21189
  | 35 => 1
  | 36 => 20529
  | 37 => 21228
  | 38 => 12
  | 39 => 1
  | 40 => 18615
  | 41 => 20128
  | 42 => 20958
  | 43 => 1
  | 44 => 243
  | 45 => 67
  | 46 => 12
  | 47 => 1
  | 48 => 4665
  | 49 => 3048
  | 50 => 1651
  | 51 => 1
  | 52 => 1431
  | 53 => 683
  | 54 => 12
  | 55 => 1
  | 56 => 1431
  | 57 => 683
  | 58 => 243
  | 59 => 1
  | 60 => 243
  | 61 => 67
  | 62 => 12
  | 63 => 1
  | _ => 0

def vtab12 (i : Fin 64) : ℕ := match i.val with
  | 0 => 40552
  | 1 => 41981
  | 2 => 42619
  | 3 => 1
  | 4 => 41761
  | 5 => 42684
  | 6 => 13
  | 7 => 1
  | 8 => 38747
  | 9 => 41122
  | 10 => 42321
  | 11 => 1
  | 12 => 311
  | 13 => 79
  | 14 => 13
  | 15 => 1
  | 16 => 34952
  | 17 => 38196
  | 18 => 40528
  | 19 => 1
  | 20 => 39956
  | 21 => 41825
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
  | 32 => 40552
  | 33 => 41981
  | 34 => 42619
  | 35 => 1
  | 36 => 41761
  | 37 => 42684
  | 38 => 13
  | 39 => 1
  | 40 => 38747
  | 41 => 41122
  | 42 => 42321
  | 43 => 1
  | 44 => 311
  | 45 => 79
  | 46 => 13
  | 47 => 1
  | 48 => 7716
  | 49 => 4723
  | 50 => 2402
  | 51 => 1
  | 52 => 2116
  | 53 => 938
  | 54 => 13
  | 55 => 1
  | 56 => 2116
  | 57 => 938
  | 58 => 311
  | 59 => 1
  | 60 => 311
  | 61 => 79
  | 62 => 13
  | 63 => 1
  | _ => 0

def vtab13 (i : Fin 64) : ℕ := match i.val with
  | 0 => 82538
  | 1 => 84652
  | 2 => 85541
  | 3 => 1
  | 4 => 84449
  | 5 => 85640
  | 6 => 14
  | 7 => 1
  | 8 => 79873
  | 9 => 83482
  | 10 => 85164
  | 11 => 1
  | 12 => 391
  | 13 => 92
  | 14 => 14
  | 15 => 1
  | 16 => 73152
  | 17 => 78763
  | 18 => 82512
  | 19 => 1
  | 20 => 81784
  | 21 => 84470
  | 22 => 14
  | 23 => 1
  | 24 => 3056
  | 25 => 1262
  | 26 => 391
  | 27 => 1
  | 28 => 391
  | 29 => 92
  | 30 => 14
  | 31 => 1
  | 32 => 82538
  | 33 => 84652
  | 34 => 85541
  | 35 => 1
  | 36 => 84449
  | 37 => 85640
  | 38 => 14
  | 39 => 1
  | 40 => 79873
  | 41 => 83482
  | 42 => 85164
  | 43 => 1
  | 44 => 391
  | 45 => 92
  | 46 => 14
  | 47 => 1
  | 48 => 12442
  | 49 => 7151
  | 50 => 3420
  | 51 => 1
  | 52 => 3056
  | 53 => 1262
  | 54 => 14
  | 55 => 1
  | 56 => 3056
  | 57 => 1262
  | 58 => 391
  | 59 => 1
  | 60 => 391
  | 61 => 92
  | 62 => 14
  | 63 => 1
  | _ => 0

def vtab14 (i : Fin 64) : ℕ := match i.val with
  | 0 => 167195
  | 1 => 170249
  | 2 => 171458
  | 3 => 1
  | 4 => 170093
  | 5 => 171600
  | 6 => 15
  | 7 => 1
  | 8 => 163359
  | 9 => 168688
  | 10 => 170989
  | 11 => 1
  | 12 => 484
  | 13 => 106
  | 14 => 15
  | 15 => 1
  | 16 => 151919
  | 17 => 161317
  | 18 => 167167
  | 19 => 1
  | 20 => 166257
  | 21 => 170039
  | 22 => 15
  | 23 => 1
  | 24 => 4320
  | 25 => 1667
  | 26 => 484
  | 27 => 1
  | 28 => 484
  | 29 => 106
  | 30 => 15
  | 31 => 1
  | 32 => 167195
  | 33 => 170249
  | 34 => 171458
  | 35 => 1
  | 36 => 170093
  | 37 => 171600
  | 38 => 15
  | 39 => 1
  | 40 => 163359
  | 41 => 168688
  | 42 => 170989
  | 43 => 1
  | 44 => 484
  | 45 => 106
  | 46 => 15
  | 47 => 1
  | 48 => 19596
  | 49 => 10599
  | 50 => 4775
  | 51 => 1
  | 52 => 4320
  | 53 => 1667
  | 54 => 15
  | 55 => 1
  | 56 => 4320
  | 57 => 1667
  | 58 => 484
  | 59 => 1
  | 60 => 484
  | 61 => 106
  | 62 => 15
  | 63 => 1
  | _ => 0

def vtab15 (i : Fin 64) : ℕ := match i.val with
  | 0 => 337449
  | 1 => 341767
  | 2 => 343377
  | 3 => 1
  | 4 => 341697
  | 5 => 343572
  | 6 => 16
  | 7 => 1
  | 8 => 332051
  | 9 => 339722
  | 10 => 342802
  | 11 => 1
  | 12 => 591
  | 13 => 121
  | 14 => 16
  | 15 => 1
  | 16 => 313240
  | 17 => 328529
  | 18 => 337419
  | 19 => 1
  | 20 => 336299
  | 21 => 341527
  | 22 => 16
  | 23 => 1
  | 24 => 5989
  | 25 => 2166
  | 26 => 591
  | 27 => 1
  | 28 => 591
  | 29 => 121
  | 30 => 16
  | 31 => 1
  | 32 => 337449
  | 33 => 341767
  | 34 => 343377
  | 35 => 1
  | 36 => 341697
  | 37 => 343572
  | 38 => 16
  | 39 => 1
  | 40 => 332051
  | 41 => 339722
  | 42 => 342802
  | 43 => 1
  | 44 => 591
  | 45 => 121
  | 46 => 16
  | 47 => 1
  | 48 => 30198
  | 49 => 15404
  | 50 => 6549
  | 51 => 1
  | 52 => 5989
  | 53 => 2166
  | 54 => 16
  | 55 => 1
  | 56 => 5989
  | 57 => 2166
  | 58 => 591
  | 59 => 1
  | 60 => 591
  | 61 => 121
  | 62 => 16
  | 63 => 1
  | _ => 0

def vtab16 (i : Fin 64) : ℕ := match i.val with
  | 0 => 679221
  | 1 => 685208
  | 2 => 687313
  | 3 => 1
  | 4 => 685273
  | 5 => 687572
  | 6 => 17
  | 7 => 1
  | 8 => 671777
  | 9 => 682572
  | 10 => 686617
  | 11 => 1
  | 12 => 713
  | 13 => 137
  | 14 => 17
  | 15 => 1
  | 16 => 641773
  | 17 => 665996
  | 18 => 679189
  | 19 => 1
  | 20 => 677829
  | 21 => 684936
  | 22 => 17
  | 23 => 1
  | 24 => 8157
  | 25 => 2773
  | 26 => 713
  | 27 => 1
  | 28 => 713
  | 29 => 137
  | 30 => 17
  | 31 => 1
  | 32 => 679221
  | 33 => 685208
  | 34 => 687313
  | 35 => 1
  | 36 => 685273
  | 37 => 687572
  | 38 => 17
  | 39 => 1
  | 40 => 671777
  | 41 => 682572
  | 42 => 686617
  | 43 => 1
  | 44 => 713
  | 45 => 137
  | 46 => 17
  | 47 => 1
  | 48 => 45605
  | 49 => 21985
  | 50 => 8837
  | 51 => 1
  | 52 => 8157
  | 53 => 2773
  | 54 => 17
  | 55 => 1
  | 56 => 8157
  | 57 => 2773
  | 58 => 713
  | 59 => 1
  | 60 => 713
  | 61 => 137
  | 62 => 17
  | 63 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 64, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 64, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 64, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 64, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 64, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 64, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel
lemma v_6 : ∀ i : Fin 64, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel
lemma v_7 : ∀ i : Fin 64, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 64, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel
lemma v_9 : ∀ i : Fin 64, v 9 i = vtab9 i := by
  intro i; rw [show (9 : ℕ) = 8 + 1 from rfl, v, step]; simp only [v_8, ok2_iff]; revert i; decide +kernel
lemma v_10 : ∀ i : Fin 64, v 10 i = vtab10 i := by
  intro i; rw [show (10 : ℕ) = 9 + 1 from rfl, v, step]; simp only [v_9, ok2_iff]; revert i; decide +kernel
lemma v_11 : ∀ i : Fin 64, v 11 i = vtab11 i := by
  intro i; rw [show (11 : ℕ) = 10 + 1 from rfl, v, step]; simp only [v_10, ok2_iff]; revert i; decide +kernel
lemma v_12 : ∀ i : Fin 64, v 12 i = vtab12 i := by
  intro i; rw [show (12 : ℕ) = 11 + 1 from rfl, v, step]; simp only [v_11, ok2_iff]; revert i; decide +kernel
lemma v_13 : ∀ i : Fin 64, v 13 i = vtab13 i := by
  intro i; rw [show (13 : ℕ) = 12 + 1 from rfl, v, step]; simp only [v_12, ok2_iff]; revert i; decide +kernel
lemma v_14 : ∀ i : Fin 64, v 14 i = vtab14 i := by
  intro i; rw [show (14 : ℕ) = 13 + 1 from rfl, v, step]; simp only [v_13, ok2_iff]; revert i; decide +kernel
lemma v_15 : ∀ i : Fin 64, v 15 i = vtab15 i := by
  intro i; rw [show (15 : ℕ) = 14 + 1 from rfl, v, step]; simp only [v_14, ok2_iff]; revert i; decide +kernel
lemma v_16 : ∀ i : Fin 64, v 16 i = vtab16 i := by
  intro i; rw [show (16 : ℕ) = 15 + 1 from rfl, v, step]; simp only [v_15, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 64) : ℤ :=
  (v (m + 9) i : ℤ) - 10 * (v (m + 8) i : ℤ) + 44 * (v (m + 7) i : ℤ) - 112 * (v (m + 6) i : ℤ) + 182 * (v (m + 5) i : ℤ) - 196 * (v (m + 4) i : ℤ) + 140 * (v (m + 3) i : ℤ) - 64 * (v (m + 2) i : ℤ) + 17 * (v (m + 1) i : ℤ) - 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 64, err 1 i = 0 := by
  intro i
  change (v 10 i : ℤ) - 10 * (v 9 i : ℤ) + 44 * (v 8 i : ℤ) - 112 * (v 7 i : ℤ) + 182 * (v 6 i : ℤ) - 196 * (v 5 i : ℤ) + 140 * (v 4 i : ℤ) - 64 * (v 3 i : ℤ) + 17 * (v 2 i : ℤ) - 2 * (v 1 i : ℤ) = 0
  simp only [v_10, v_9, v_8, v_7, v_6, v_5, v_4, v_3, v_2, v_1]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 64) :
    err (m + 1) i = ∑ j : Fin 64, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 64, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 64) : err (m + 1) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_m (m : ℕ) :
    (a (m + 10) : ℤ) = 10 * a (m + 9) - 44 * a (m + 8) + 112 * a (m + 7) - 182 * a (m + 6) + 196 * a (m + 5) - 140 * a (m + 4) + 64 * a (m + 3) - 17 * a (m + 2) + 2 * a (m + 1) := by
  have h : ∑ i : Fin 64, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 64, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 64, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  have h2_5 : m + 1 + 5 = m + 6 := by omega
  have h2_6 : m + 1 + 6 = m + 7 := by omega
  have h2_7 : m + 1 + 7 = m + 8 := by omega
  have h2_8 : m + 1 + 8 = m + 9 := by omega
  have h2_9 : m + 1 + 9 = m + 10 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5, h2_6, h2_7, h2_8, h2_9] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 209 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 1 i = 209
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 518 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 2 i = 518
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 1194 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 3 i = 1194
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 2640 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 4 i = 2640
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 5688 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 5 i = 5688
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 12036 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 6 i = 12036
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 25126 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 7 i = 25126
  simp only [v_7]; decide +kernel
lemma a_8 : a 8 = 51904 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 8 i = 51904
  simp only [v_8]; decide +kernel
lemma a_9 : a 9 = 106344 := by
  rw [show (9 : ℕ) = 8 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 9 i = 106344
  simp only [v_9]; decide +kernel
lemma a_10 : a 10 = 216500 := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 10 i = 216500
  simp only [v_10]; decide +kernel
lemma a_11 : a 11 = 438614 := by
  rw [show (11 : ℕ) = 10 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 11 i = 438614
  simp only [v_11]; decide +kernel
lemma a_12 : a 12 = 885336 := by
  rw [show (12 : ℕ) = 11 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 12 i = 885336
  simp only [v_12]; decide +kernel
lemma a_13 : a 13 = 1782168 := by
  rw [show (13 : ℕ) = 12 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 13 i = 1782168
  simp only [v_13]; decide +kernel
lemma a_14 : a 14 = 3580356 := by
  rw [show (14 : ℕ) = 13 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 14 i = 3580356
  simp only [v_14]; decide +kernel
lemma a_15 : a 15 = 7182678 := by
  rw [show (15 : ℕ) = 14 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 15 i = 7182678
  simp only [v_15]; decide +kernel
lemma a_16 : a 16 = 14395024 := by
  rw [show (16 : ℕ) = 15 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 16 i = 14395024
  simp only [v_16]; decide +kernel

def e (m : ℕ) : ℤ := (a (m + 8) : ℤ) - (8 * a (m + 7) - 27 * a (m + 6) + 50 * a (m + 5) - 55 * a (m + 4) + 36 * a (m + 3) - 13 * a (m + 2) + 2 * a (m + 1))

lemma e_rec (m : ℕ) : e (m + 9) = 10 * e (m + 8) - 44 * e (m + 7) + 112 * e (m + 6) - 182 * e (m + 5) + 196 * e (m + 4) - 140 * e (m + 3) + 64 * e (m + 2) - 17 * e (m + 1) + 2 * e m := by
  have g0 : (a (m + 17) : ℤ) = 10 * a (m + 16) - 44 * a (m + 15) + 112 * a (m + 14) - 182 * a (m + 13) + 196 * a (m + 12) - 140 * a (m + 11) + 64 * a (m + 10) - 17 * a (m + 9) + 2 * a (m + 8) := by
    have h := a_rec_m (m + 7)
    simp only [show m + 7 + 10 = m + 17 by omega, show m + 7 + 9 = m + 16 by omega, show m + 7 + 8 = m + 15 by omega, show m + 7 + 7 = m + 14 by omega, show m + 7 + 6 = m + 13 by omega, show m + 7 + 5 = m + 12 by omega, show m + 7 + 4 = m + 11 by omega, show m + 7 + 3 = m + 10 by omega, show m + 7 + 2 = m + 9 by omega, show m + 7 + 1 = m + 8 by omega] at h
    exact h
  have g1 : (a (m + 16) : ℤ) = 10 * a (m + 15) - 44 * a (m + 14) + 112 * a (m + 13) - 182 * a (m + 12) + 196 * a (m + 11) - 140 * a (m + 10) + 64 * a (m + 9) - 17 * a (m + 8) + 2 * a (m + 7) := by
    have h := a_rec_m (m + 6)
    simp only [show m + 6 + 10 = m + 16 by omega, show m + 6 + 9 = m + 15 by omega, show m + 6 + 8 = m + 14 by omega, show m + 6 + 7 = m + 13 by omega, show m + 6 + 6 = m + 12 by omega, show m + 6 + 5 = m + 11 by omega, show m + 6 + 4 = m + 10 by omega, show m + 6 + 3 = m + 9 by omega, show m + 6 + 2 = m + 8 by omega, show m + 6 + 1 = m + 7 by omega] at h
    exact h
  have g2 : (a (m + 15) : ℤ) = 10 * a (m + 14) - 44 * a (m + 13) + 112 * a (m + 12) - 182 * a (m + 11) + 196 * a (m + 10) - 140 * a (m + 9) + 64 * a (m + 8) - 17 * a (m + 7) + 2 * a (m + 6) := by
    have h := a_rec_m (m + 5)
    simp only [show m + 5 + 10 = m + 15 by omega, show m + 5 + 9 = m + 14 by omega, show m + 5 + 8 = m + 13 by omega, show m + 5 + 7 = m + 12 by omega, show m + 5 + 6 = m + 11 by omega, show m + 5 + 5 = m + 10 by omega, show m + 5 + 4 = m + 9 by omega, show m + 5 + 3 = m + 8 by omega, show m + 5 + 2 = m + 7 by omega, show m + 5 + 1 = m + 6 by omega] at h
    exact h
  have g3 : (a (m + 14) : ℤ) = 10 * a (m + 13) - 44 * a (m + 12) + 112 * a (m + 11) - 182 * a (m + 10) + 196 * a (m + 9) - 140 * a (m + 8) + 64 * a (m + 7) - 17 * a (m + 6) + 2 * a (m + 5) := by
    have h := a_rec_m (m + 4)
    simp only [show m + 4 + 10 = m + 14 by omega, show m + 4 + 9 = m + 13 by omega, show m + 4 + 8 = m + 12 by omega, show m + 4 + 7 = m + 11 by omega, show m + 4 + 6 = m + 10 by omega, show m + 4 + 5 = m + 9 by omega, show m + 4 + 4 = m + 8 by omega, show m + 4 + 3 = m + 7 by omega, show m + 4 + 2 = m + 6 by omega, show m + 4 + 1 = m + 5 by omega] at h
    exact h
  have g4 : (a (m + 13) : ℤ) = 10 * a (m + 12) - 44 * a (m + 11) + 112 * a (m + 10) - 182 * a (m + 9) + 196 * a (m + 8) - 140 * a (m + 7) + 64 * a (m + 6) - 17 * a (m + 5) + 2 * a (m + 4) := by
    have h := a_rec_m (m + 3)
    simp only [show m + 3 + 10 = m + 13 by omega, show m + 3 + 9 = m + 12 by omega, show m + 3 + 8 = m + 11 by omega, show m + 3 + 7 = m + 10 by omega, show m + 3 + 6 = m + 9 by omega, show m + 3 + 5 = m + 8 by omega, show m + 3 + 4 = m + 7 by omega, show m + 3 + 3 = m + 6 by omega, show m + 3 + 2 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega] at h
    exact h
  have g5 : (a (m + 12) : ℤ) = 10 * a (m + 11) - 44 * a (m + 10) + 112 * a (m + 9) - 182 * a (m + 8) + 196 * a (m + 7) - 140 * a (m + 6) + 64 * a (m + 5) - 17 * a (m + 4) + 2 * a (m + 3) := by
    have h := a_rec_m (m + 2)
    simp only [show m + 2 + 10 = m + 12 by omega, show m + 2 + 9 = m + 11 by omega, show m + 2 + 8 = m + 10 by omega, show m + 2 + 7 = m + 9 by omega, show m + 2 + 6 = m + 8 by omega, show m + 2 + 5 = m + 7 by omega, show m + 2 + 4 = m + 6 by omega, show m + 2 + 3 = m + 5 by omega, show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at h
    exact h
  have g6 : (a (m + 11) : ℤ) = 10 * a (m + 10) - 44 * a (m + 9) + 112 * a (m + 8) - 182 * a (m + 7) + 196 * a (m + 6) - 140 * a (m + 5) + 64 * a (m + 4) - 17 * a (m + 3) + 2 * a (m + 2) := by
    have h := a_rec_m (m + 1)
    simp only [show m + 1 + 10 = m + 11 by omega, show m + 1 + 9 = m + 10 by omega, show m + 1 + 8 = m + 9 by omega, show m + 1 + 7 = m + 8 by omega, show m + 1 + 6 = m + 7 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h
    exact h
  have g7 : (a (m + 10) : ℤ) = 10 * a (m + 9) - 44 * a (m + 8) + 112 * a (m + 7) - 182 * a (m + 6) + 196 * a (m + 5) - 140 * a (m + 4) + 64 * a (m + 3) - 17 * a (m + 2) + 2 * a (m + 1) := by
    have h := a_rec_m (m + 0)
    simp only [show m + 0 + 10 = m + 10 by omega, show m + 0 + 9 = m + 9 by omega, show m + 0 + 8 = m + 8 by omega, show m + 0 + 7 = m + 7 by omega, show m + 0 + 6 = m + 6 by omega, show m + 0 + 5 = m + 5 by omega, show m + 0 + 4 = m + 4 by omega, show m + 0 + 3 = m + 3 by omega, show m + 0 + 2 = m + 2 by omega, show m + 0 + 1 = m + 1 by omega] at h
    exact h
  simp only [e, show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 6 = m + 7 by omega, show m + 1 + 7 = m + 8 by omega, show m + 1 + 8 = m + 9 by omega, show m + 2 + 1 = m + 3 by omega, show m + 2 + 2 = m + 4 by omega, show m + 2 + 3 = m + 5 by omega, show m + 2 + 4 = m + 6 by omega, show m + 2 + 5 = m + 7 by omega, show m + 2 + 6 = m + 8 by omega, show m + 2 + 7 = m + 9 by omega, show m + 2 + 8 = m + 10 by omega, show m + 3 + 1 = m + 4 by omega, show m + 3 + 2 = m + 5 by omega, show m + 3 + 3 = m + 6 by omega, show m + 3 + 4 = m + 7 by omega, show m + 3 + 5 = m + 8 by omega, show m + 3 + 6 = m + 9 by omega, show m + 3 + 7 = m + 10 by omega, show m + 3 + 8 = m + 11 by omega, show m + 4 + 1 = m + 5 by omega, show m + 4 + 2 = m + 6 by omega, show m + 4 + 3 = m + 7 by omega, show m + 4 + 4 = m + 8 by omega, show m + 4 + 5 = m + 9 by omega, show m + 4 + 6 = m + 10 by omega, show m + 4 + 7 = m + 11 by omega, show m + 4 + 8 = m + 12 by omega, show m + 5 + 1 = m + 6 by omega, show m + 5 + 2 = m + 7 by omega, show m + 5 + 3 = m + 8 by omega, show m + 5 + 4 = m + 9 by omega, show m + 5 + 5 = m + 10 by omega, show m + 5 + 6 = m + 11 by omega, show m + 5 + 7 = m + 12 by omega, show m + 5 + 8 = m + 13 by omega, show m + 6 + 1 = m + 7 by omega, show m + 6 + 2 = m + 8 by omega, show m + 6 + 3 = m + 9 by omega, show m + 6 + 4 = m + 10 by omega, show m + 6 + 5 = m + 11 by omega, show m + 6 + 6 = m + 12 by omega, show m + 6 + 7 = m + 13 by omega, show m + 6 + 8 = m + 14 by omega, show m + 7 + 1 = m + 8 by omega, show m + 7 + 2 = m + 9 by omega, show m + 7 + 3 = m + 10 by omega, show m + 7 + 4 = m + 11 by omega, show m + 7 + 5 = m + 12 by omega, show m + 7 + 6 = m + 13 by omega, show m + 7 + 7 = m + 14 by omega, show m + 7 + 8 = m + 15 by omega, show m + 8 + 1 = m + 9 by omega, show m + 8 + 2 = m + 10 by omega, show m + 8 + 3 = m + 11 by omega, show m + 8 + 4 = m + 12 by omega, show m + 8 + 5 = m + 13 by omega, show m + 8 + 6 = m + 14 by omega, show m + 8 + 7 = m + 15 by omega, show m + 8 + 8 = m + 16 by omega, show m + 9 + 1 = m + 10 by omega, show m + 9 + 2 = m + 11 by omega, show m + 9 + 3 = m + 12 by omega, show m + 9 + 4 = m + 13 by omega, show m + 9 + 5 = m + 14 by omega, show m + 9 + 6 = m + 15 by omega, show m + 9 + 7 = m + 16 by omega, show m + 9 + 8 = m + 17 by omega]
  linear_combination (1) * g0 + (-8) * g1 + (27) * g2 + (-50) * g3 + (55) * g4 + (-36) * g5 + (13) * g6 + (-2) * g7

lemma e_zero : ∀ m : ℕ, e m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 9 with h | h
    · interval_cases m <;> norm_num [e, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13, a_14, a_15, a_16]
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 9 := ⟨m - 9, by omega⟩
      rw [e_rec t]
      simp [ih (t + 8) (by omega), ih (t + 7) (by omega), ih (t + 6) (by omega), ih (t + 5) (by omega), ih (t + 4) (by omega), ih (t + 3) (by omega), ih (t + 2) (by omega), ih (t + 1) (by omega), ih t (by omega)]

lemma a_rec_ge (m : ℕ) :
    (a (m + 8) : ℤ) = 8 * a (m + 7) - 27 * a (m + 6) + 50 * a (m + 5) - 55 * a (m + 4) + 36 * a (m + 3) - 13 * a (m + 2) + 2 * a (m + 1) := by
  have h := e_zero m
  unfold e at h
  linarith

def cf (n : ℕ) : ℚ :=
  (9 / 2 : ℚ) * (49 * (2 : ℚ) ^ n - 32) - (374 * (n : ℚ)) / 5 - 9 * (n : ℚ) ^ 2 - (25 * (n : ℚ) ^ 3) / 6 - (n : ℚ) ^ 5 / 30


theorem main_proof_ours :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 6 * (1 - 2 * X)) =
      X * (209 - 1154 * X + 2693 * X ^ 2 - 3376 * X ^ 3 + 2401 * X ^ 4 - 922 * X ^ 5 + 153 * X ^ 6)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (9 / 2 : ℚ) * (49 * (2 : ℚ) ^ n - 32) - (374 * (n : ℚ)) / 5 - 9 * (n : ℚ) ^ 2 - (25 * (n : ℚ) ^ 3) / 6 - (n : ℚ) ^ 5 / 30) := by
  have hrec : ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 6 * (1 - 2 * X)) =
      X * (209 - 1154 * X + 2693 * X ^ 2 - 3376 * X ^ 3 + 2401 * X ^ 4 - 922 * X ^ 5 + 153 * X ^ 6) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 6 * (1 - 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (8 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (27 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (50 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (55 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (36 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        + C (13 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (209 - 1154 * X + 2693 * X ^ 2 - 3376 * X ^ 3 + 2401 * X ^ 4 - 922 * X ^ 5 + 153 * X ^ 6) : PowerSeries ℚ) =
        C (209 : ℚ) * X ^ 1 - C (1154 : ℚ) * X ^ 2 + C (2693 : ℚ) * X ^ 3 - C (3376 : ℚ) * X ^ 4 + C (2401 : ℚ) * X ^ 5 - C (922 : ℚ) * X ^ 6 + C (153 : ℚ) * X ^ 7 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13, a_14, a_15, a_16] <;> try norm_num
    · have hq : (a n : ℚ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7) := by
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
      simp only [c1, c2, c3, c4, c5, c6, c7, e1, e2, e3, e4, e5, e6, e7, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (9 / 2 : ℚ) * (49 * (2 : ℚ) ^ n - 32) - (374 * (n : ℚ)) / 5 - 9 * (n : ℚ) ^ 2 - (25 * (n : ℚ) ^ 3) / 6 - (n : ℚ) ^ 5 / 30 := by
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
    have hb_6 : (a 6 : ℚ) = cf 6 := by
      rw [a_6]; unfold cf
      push_cast
      norm_num
    have hb_7 : (a 7 : ℚ) = cf 7 := by
      rw [a_7]; unfold cf
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 8) = 8 * cf (m + 7) - 27 * cf (m + 6) + 50 * cf (m + 5) - 55 * cf (m + 4) + 36 * cf (m + 3) - 13 * cf (m + 2) + 2 * cf (m + 1) := by
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
      have hp_t_6 : (2 : ℚ) ^ (m + 7) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 6 := by
        rw [show m + 7 = (m + 1) + 6 by omega, pow_add]
      have hp_t_7 : (2 : ℚ) ^ (m + 8) = (2 : ℚ) ^ (m + 1) * (2 : ℚ) ^ 7 := by
        rw [show m + 8 = (m + 1) + 7 by omega, pow_add]
      simp only [hp_t_1, hp_t_2, hp_t_3, hp_t_4, hp_t_5, hp_t_6, hp_t_7]
      generalize (2 : ℚ) ^ (m + 1) = Xt
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 1) : ℚ) = cf (m + 1) ∧
        (a (m + 2) : ℚ) = cf (m + 2) ∧
        (a (m + 3) : ℚ) = cf (m + 3) ∧
        (a (m + 4) : ℚ) = cf (m + 4) ∧
        (a (m + 5) : ℚ) = cf (m + 5) ∧
        (a (m + 6) : ℚ) = cf (m + 6) ∧
        (a (m + 7) : ℚ) = cf (m + 7) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_1, hb_2, hb_3, hb_4, hb_5, hb_6, hb_7⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), (by simpa only [show m + 1 + 3 = m + 4 by omega] using h3), (by simpa only [show m + 1 + 4 = m + 5 by omega] using h4), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h5), (by simpa only [show m + 1 + 6 = m + 7 by omega] using h6), ?_⟩
        rw [show m + 1 + 7 = m + 8 by omega]
        have hr : (a (m + 8) : ℚ) = 8 * a (m + 7) - 27 * a (m + 6) + 50 * a (m + 5) - 55 * a (m + 4) + 36 * a (m + 3) - 13 * a (m + 2) + 2 * a (m + 1) := by
          have h0' := hrec (m + 8) (by omega)
          simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h6, h5, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 2, OMA.S_oeis_a250780.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250780.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250780.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250780.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250780.main := by
  obtain ⟨hrec, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250780.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250780.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega), hA (n - 4) (by omega), hA (n - 5) (by omega), hA (n - 6) (by omega), hA (n - 7) (by omega)]
    exact hrec n hn
  · rw [hser, OMA.S_oeis_a250780.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n (by omega)]; exact hcf n hn

end OMA.P250780

theorem OMA.solution : type_of% @OMA.S_oeis_a250780.main := OMA.P250780.main_proof
