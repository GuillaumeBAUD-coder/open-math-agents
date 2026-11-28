import OMAStatements.S_oeis_a250854

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence and closed form bridged to upstream Blk/Good encoding.

namespace OMA.P250854

open PowerSeries

/-- A `2 X 2` `0..3` subblock `(a, b / c, d)` has `b - a ≤ d - c` (in `ℤ`) and `min a c ≤ min b d`. -/
def okBlock (a b c d : Fin 4) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ min a.val c.val ≤ min b.val d.val

instance (a b c d : Fin 4) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- A `3 X (m + 1)` `0..3` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin 3 → Fin (m + 1) → Fin 4) : Prop :=
  ∀ i : Fin 2, ∀ j : Fin m,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin 3 → Fin (m + 1) → Fin 4) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250854: Number of (2+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250854 PowerSeries

abbrev Col := Fin 3 → Fin 4

def okCol (c₁ c₂ : Col) : Prop :=
  ∀ i : Fin 2, okBlock (c₁ i.castSucc) (c₂ i.castSucc) (c₁ i.succ) (c₂ i.succ)

instance (c₁ c₂ : Col) : Decidable (okCol c₁ c₂) := by
  unfold okCol; infer_instance

def isValidT (m : ℕ) (y : Fin (m + 1) → Col) : Prop :=
  ∀ j : Fin m, okCol (y j.castSucc) (y j.succ)

instance (m : ℕ) (y : Fin (m + 1) → Col) : Decidable (isValidT m y) := by
  unfold isValidT; infer_instance

lemma isValid_transpose (m : ℕ) (y : Fin (m + 1) → Col) :
    isValid m (fun i j => y j i) ↔ isValidT m y :=
  forall_comm

def enc (c : Col) : Fin 64 :=
  ⟨16 * (c 0).val + 4 * (c 1).val + (c 2).val, by
    have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; omega⟩

def dec (k : Fin 64) : Col := fun r =>
  have hk := k.isLt
  if r.val = 0 then ⟨k.val / 16, by omega⟩
  else if r.val = 1 then ⟨(k.val / 4) % 4, by omega⟩
  else ⟨k.val % 4, by omega⟩

lemma enc_dec : ∀ k : Fin 64, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ c : Col, dec (enc c) = c := by
  intro c; ext r
  have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt
  fin_cases r
  · change (dec (enc c) 0).val = (c 0).val; simp [dec, enc]; try omega
  · change (dec (enc c) 1).val = (c 1).val; simp [dec, enc]; try omega
  · change (dec (enc c) 2).val = (c 2).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 64) : Prop := okCol (dec i) (dec j)

instance (i j : Fin 64) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 64) : ℕ := match i.val with
  | 0 => 9223525970846190831
  | 1 => 8796239825102
  | 2 => 8388748
  | 3 => 8
  | 4 => 211109688692464
  | 5 => 140739837201632
  | 6 => 134219968
  | 7 => 128
  | 8 => 3758157568
  | 9 => 3221278208
  | 10 => 2147519488
  | 11 => 2048
  | 12 => 61440
  | 13 => 57344
  | 14 => 49152
  | 15 => 32768
  | 16 => 10088218061374983407
  | 17 => 576470373177886926
  | 18 => 549764989068
  | 19 => 524296
  | 20 => 13835284558149320704
  | 21 => 9223525970846154752
  | 22 => 8796239822848
  | 23 => 8388608
  | 24 => 246294614376448
  | 25 => 211109688639488
  | 26 => 140739837165568
  | 27 => 134217728
  | 28 => 4026531840
  | 29 => 3758096384
  | 30 => 3221225472
  | 31 => 2147483648
  | 32 => 10151268520582679791
  | 33 => 630513628835875022
  | 34 => 36029398323560588
  | 35 => 34360262664
  | 36 => 14844091905472462848
  | 37 => 10088218061373964288
  | 38 => 576470373176967168
  | 39 => 549764202496
  | 40 => 16141163847774896128
  | 41 => 13835284554677485568
  | 42 => 9223525968482664448
  | 43 => 8796093022208
  | 44 => 263882790666240
  | 45 => 246290604621824
  | 46 => 211106232532992
  | 47 => 140737488355328
  | 48 => 10155490645233339631
  | 49 => 634454278509824206
  | 50 => 39407098044088460
  | 51 => 2251834173947912
  | 52 => 14911645899883020288
  | 53 => 10151268456157151232
  | 54 => 630513568705413120
  | 55 => 36029346783166464
  | 56 => 17222027758343815168
  | 57 => 14844090871208476672
  | 58 => 10088217096937799680
  | 59 => 576469548396445696
  | 60 => 17293822569102704640
  | 61 => 16140901064495857664
  | 62 => 13835058055282163712
  | 63 => 9223372036854775808
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 64, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 64 → ℕ) (i : Fin 64) : ℕ :=
  ∑ j : Fin 64, if ok2 i j then f j else 0

def v : ℕ → Fin 64 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Col) → ℕ) :
    ∑ x, f x = ∑ c : Col, ∑ y : Fin (m + 1) → Col, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Col) → ℕ) :
    ∑ y, g y = ∑ i : Fin 64, ∑ y : Fin (m + 1) → Col, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Col, ∑ i : Fin 64, if enc (y 0) = i then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0))]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  · exact Finset.sum_comm

lemma isValidT_zero (y : Fin 1 → Col) : isValidT 0 y := by
  intro j; exact Fin.elim0 j

lemma isValidT_cons (m : ℕ) (c : Col) (y : Fin (m + 1) → Col) :
    isValidT (m + 1) (Fin.cons c y) ↔ okCol c (y 0) ∧ isValidT m y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h 0
    · intro j
      simpa using h j.succ
  · rintro ⟨h0, hy⟩ j
    refine Fin.cases ?_ (fun j' => ?_) j
    · simpa [Fin.castSucc_zero, Fin.succ_zero_eq_one] using h0
    · simpa using hy j'

lemma v_eq (m : ℕ) (i : Fin 64) :
    v m i = ∑ y : Fin (m + 1) → Col, if enc (y 0) = i ∧ isValidT m y then 1 else 0 := by
  induction m generalizing i with
  | zero =>
    rw [v, ← (Equiv.funUnique (Fin 1) Col).symm.sum_comp]
    rw [Finset.sum_eq_single (dec i)]
    · have hu : (Equiv.funUnique (Fin 1) Col).symm (dec i) = fun _ : Fin 1 => dec i := funext fun _ => rfl
      rw [hu]
      simp [enc_dec, isValidT_zero]
    · intro c _ hc
      have hne : enc c ≠ i := fun h => hc (by rw [← dec_enc c, h])
      have hu : (Equiv.funUnique (Fin 1) Col).symm c = fun _ : Fin 1 => c := funext fun _ => rfl
      rw [hu]
      simp [hne]
    · simp
  | succ m ih =>
    rw [v, step, sum_cons]
    rw [Finset.sum_eq_single (dec i)]
    · simp only [Fin.cons_zero, enc_dec, true_and, isValidT_cons]
      rw [fiber]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j]
      by_cases h : ok2 i j
      · simp only [h, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : enc (y 0) = j
        · have hok : okCol (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hok]
        · simp [hy]
      · simp only [h, ↓reduceIte]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : enc (y 0) = j
        · have hnok : ¬ okCol (dec i) (y 0) := by
            rw [← dec_enc (y 0), hy]; exact h
          simp [hy, hnok]
        · simp [hy]
    · intro c _ hc
      have hne : enc c ≠ i := fun h => hc (by rw [← dec_enc c, h])
      apply Finset.sum_eq_zero
      intro y _
      simp [hne]
    · simp

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 64, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [← (Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 2)) => Fin 4)).symm.sum_comp]
  have htr : ∀ y : Fin (n + 2) → Col,
      isValid (n + 1) ((Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 2)) => Fin 4)).symm y) ↔
      isValidT (n + 1) y := fun y => isValid_transpose (n + 1) y
  simp only [htr]
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
  | 0 => 20
  | 1 => 10
  | 2 => 4
  | 3 => 1
  | 4 => 16
  | 5 => 10
  | 6 => 4
  | 7 => 1
  | 8 => 10
  | 9 => 7
  | 10 => 4
  | 11 => 1
  | 12 => 4
  | 13 => 3
  | 14 => 2
  | 15 => 1
  | 16 => 29
  | 17 => 16
  | 18 => 7
  | 19 => 2
  | 20 => 16
  | 21 => 10
  | 22 => 4
  | 23 => 1
  | 24 => 10
  | 25 => 7
  | 26 => 4
  | 27 => 1
  | 28 => 4
  | 29 => 3
  | 30 => 2
  | 31 => 1
  | 32 => 36
  | 33 => 21
  | 34 => 10
  | 35 => 3
  | 36 => 23
  | 37 => 15
  | 38 => 7
  | 39 => 2
  | 40 => 10
  | 41 => 7
  | 42 => 4
  | 43 => 1
  | 44 => 4
  | 45 => 3
  | 46 => 2
  | 47 => 1
  | 48 => 40
  | 49 => 24
  | 50 => 12
  | 51 => 4
  | 52 => 27
  | 53 => 18
  | 54 => 9
  | 55 => 3
  | 56 => 14
  | 57 => 10
  | 58 => 6
  | 59 => 2
  | 60 => 4
  | 61 => 3
  | 62 => 2
  | 63 => 1
  | _ => 0
def vtab2 (i : Fin 64) : ℕ := match i.val with
  | 0 => 84
  | 1 => 28
  | 2 => 7
  | 3 => 1
  | 4 => 64
  | 5 => 28
  | 6 => 7
  | 7 => 1
  | 8 => 34
  | 9 => 18
  | 10 => 7
  | 11 => 1
  | 12 => 10
  | 13 => 6
  | 14 => 3
  | 15 => 1
  | 16 => 170
  | 17 => 64
  | 18 => 18
  | 19 => 3
  | 20 => 64
  | 21 => 28
  | 22 => 7
  | 23 => 1
  | 24 => 34
  | 25 => 18
  | 26 => 7
  | 27 => 1
  | 28 => 10
  | 29 => 6
  | 30 => 3
  | 31 => 1
  | 32 => 270
  | 33 => 110
  | 34 => 34
  | 35 => 6
  | 36 => 129
  | 37 => 60
  | 38 => 18
  | 39 => 3
  | 40 => 34
  | 41 => 18
  | 42 => 7
  | 43 => 1
  | 44 => 10
  | 45 => 6
  | 46 => 3
  | 47 => 1
  | 48 => 350
  | 49 => 150
  | 50 => 50
  | 51 => 10
  | 52 => 186
  | 53 => 90
  | 54 => 30
  | 55 => 6
  | 56 => 66
  | 57 => 36
  | 58 => 15
  | 59 => 3
  | 60 => 10
  | 61 => 6
  | 62 => 3
  | 63 => 1
  | _ => 0
def vtab3 (i : Fin 64) : ℕ := match i.val with
  | 0 => 220
  | 1 => 55
  | 2 => 10
  | 3 => 1
  | 4 => 164
  | 5 => 55
  | 6 => 10
  | 7 => 1
  | 8 => 80
  | 9 => 34
  | 10 => 10
  | 11 => 1
  | 12 => 20
  | 13 => 10
  | 14 => 4
  | 15 => 1
  | 16 => 574
  | 17 => 164
  | 18 => 34
  | 19 => 4
  | 20 => 164
  | 21 => 55
  | 22 => 10
  | 23 => 1
  | 24 => 80
  | 25 => 34
  | 26 => 10
  | 27 => 1
  | 28 => 20
  | 29 => 10
  | 30 => 4
  | 31 => 1
  | 32 => 1120
  | 33 => 350
  | 34 => 80
  | 35 => 10
  | 36 => 428
  | 37 => 154
  | 38 => 34
  | 39 => 4
  | 40 => 80
  | 41 => 34
  | 42 => 10
  | 43 => 1
  | 44 => 20
  | 45 => 10
  | 46 => 4
  | 47 => 1
  | 48 => 1680
  | 49 => 560
  | 50 => 140
  | 51 => 20
  | 52 => 740
  | 53 => 280
  | 54 => 70
  | 55 => 10
  | 56 => 200
  | 57 => 88
  | 58 => 28
  | 59 => 4
  | 60 => 20
  | 61 => 10
  | 62 => 4
  | 63 => 1
  | _ => 0
def vtab4 (i : Fin 64) : ℕ := match i.val with
  | 0 => 455
  | 1 => 91
  | 2 => 13
  | 3 => 1
  | 4 => 335
  | 5 => 91
  | 6 => 13
  | 7 => 1
  | 8 => 155
  | 9 => 55
  | 10 => 13
  | 11 => 1
  | 12 => 35
  | 13 => 15
  | 14 => 5
  | 15 => 1
  | 16 => 1455
  | 17 => 335
  | 18 => 55
  | 19 => 5
  | 20 => 335
  | 21 => 91
  | 22 => 13
  | 23 => 1
  | 24 => 155
  | 25 => 55
  | 26 => 13
  | 27 => 1
  | 28 => 35
  | 29 => 15
  | 30 => 5
  | 31 => 1
  | 32 => 3375
  | 33 => 855
  | 34 => 155
  | 35 => 15
  | 36 => 1075
  | 37 => 315
  | 38 => 55
  | 39 => 5
  | 40 => 155
  | 41 => 55
  | 42 => 13
  | 43 => 1
  | 44 => 35
  | 45 => 15
  | 46 => 5
  | 47 => 1
  | 48 => 5775
  | 49 => 1575
  | 50 => 315
  | 51 => 35
  | 52 => 2175
  | 53 => 675
  | 54 => 135
  | 55 => 15
  | 56 => 475
  | 57 => 175
  | 58 => 45
  | 59 => 5
  | 60 => 35
  | 61 => 15
  | 62 => 5
  | 63 => 1
  | _ => 0
def vtab5 (i : Fin 64) : ℕ := match i.val with
  | 0 => 816
  | 1 => 136
  | 2 => 16
  | 3 => 1
  | 4 => 596
  | 5 => 136
  | 6 => 16
  | 7 => 1
  | 8 => 266
  | 9 => 81
  | 10 => 16
  | 11 => 1
  | 12 => 56
  | 13 => 21
  | 14 => 6
  | 15 => 1
  | 16 => 3091
  | 17 => 596
  | 18 => 81
  | 19 => 6
  | 20 => 596
  | 21 => 136
  | 22 => 16
  | 23 => 1
  | 24 => 266
  | 25 => 81
  | 26 => 16
  | 27 => 1
  | 28 => 56
  | 29 => 21
  | 30 => 6
  | 31 => 1
  | 32 => 8316
  | 33 => 1771
  | 34 => 266
  | 35 => 21
  | 36 => 2271
  | 37 => 561
  | 38 => 81
  | 39 => 6
  | 40 => 266
  | 41 => 81
  | 42 => 16
  | 43 => 1
  | 44 => 56
  | 45 => 21
  | 46 => 6
  | 47 => 1
  | 48 => 16016
  | 49 => 3696
  | 50 => 616
  | 51 => 56
  | 52 => 5271
  | 53 => 1386
  | 54 => 231
  | 55 => 21
  | 56 => 966
  | 57 => 306
  | 58 => 66
  | 59 => 6
  | 60 => 56
  | 61 => 21
  | 62 => 6
  | 63 => 1
  | _ => 0
def vtab6 (i : Fin 64) : ℕ := match i.val with
  | 0 => 1330
  | 1 => 190
  | 2 => 19
  | 3 => 1
  | 4 => 966
  | 5 => 190
  | 6 => 19
  | 7 => 1
  | 8 => 420
  | 9 => 112
  | 10 => 19
  | 11 => 1
  | 12 => 84
  | 13 => 28
  | 14 => 7
  | 15 => 1
  | 16 => 5824
  | 17 => 966
  | 18 => 112
  | 19 => 7
  | 20 => 966
  | 21 => 190
  | 22 => 19
  | 23 => 1
  | 24 => 420
  | 25 => 112
  | 26 => 19
  | 27 => 1
  | 28 => 84
  | 29 => 28
  | 30 => 7
  | 31 => 1
  | 32 => 17836
  | 33 => 3276
  | 34 => 420
  | 35 => 28
  | 36 => 4263
  | 37 => 910
  | 38 => 112
  | 39 => 7
  | 40 => 420
  | 41 => 112
  | 42 => 19
  | 43 => 1
  | 44 => 84
  | 45 => 28
  | 46 => 7
  | 47 => 1
  | 48 => 38220
  | 49 => 7644
  | 50 => 1092
  | 51 => 84
  | 52 => 11172
  | 53 => 2548
  | 54 => 364
  | 55 => 28
  | 56 => 1764
  | 57 => 490
  | 58 => 91
  | 59 => 7
  | 60 => 84
  | 61 => 28
  | 62 => 7
  | 63 => 1
  | _ => 0
def vtab7 (i : Fin 64) : ℕ := match i.val with
  | 0 => 2024
  | 1 => 253
  | 2 => 22
  | 3 => 1
  | 4 => 1464
  | 5 => 253
  | 6 => 22
  | 7 => 1
  | 8 => 624
  | 9 => 148
  | 10 => 22
  | 11 => 1
  | 12 => 120
  | 13 => 36
  | 14 => 8
  | 15 => 1
  | 16 => 10060
  | 17 => 1464
  | 18 => 148
  | 19 => 8
  | 20 => 1464
  | 21 => 253
  | 22 => 22
  | 23 => 1
  | 24 => 624
  | 25 => 148
  | 26 => 22
  | 27 => 1
  | 28 => 120
  | 29 => 36
  | 30 => 8
  | 31 => 1
  | 32 => 34560
  | 33 => 5580
  | 34 => 624
  | 35 => 36
  | 36 => 7344
  | 37 => 1380
  | 38 => 148
  | 39 => 8
  | 40 => 624
  | 41 => 148
  | 42 => 22
  | 43 => 1
  | 44 => 120
  | 45 => 36
  | 46 => 8
  | 47 => 1
  | 48 => 81600
  | 49 => 14400
  | 50 => 1800
  | 51 => 120
  | 52 => 21456
  | 53 => 4320
  | 54 => 540
  | 55 => 36
  | 56 => 2976
  | 57 => 736
  | 58 => 120
  | 59 => 8
  | 60 => 120
  | 61 => 36
  | 62 => 8
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

def err (m : ℕ) (i : Fin 64) : ℤ :=
  (v (m + 7) i : ℤ) - 7 * (v (m + 6) i : ℤ) + 21 * (v (m + 5) i : ℤ) - 35 * (v (m + 4) i : ℤ) + 35 * (v (m + 3) i : ℤ) - 21 * (v (m + 2) i : ℤ) + 7 * (v (m + 1) i : ℤ) - (v m i : ℤ)

lemma err_base : ∀ i : Fin 64, err 0 i = 0 := by
  intro i
  change (v 7 i : ℤ) - 7 * (v 6 i : ℤ) + 21 * (v 5 i : ℤ) - 35 * (v 4 i : ℤ) + 35 * (v 3 i : ℤ) - 21 * (v 2 i : ℤ) + 7 * (v 1 i : ℤ) - (v 0 i : ℤ) = 0
  simp only [v_7, v_6, v_5, v_4, v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 64) :
    err (m + 1) i = ∑ j : Fin 64, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 64, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step, Nat.cast_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> rfl
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 64) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 8) : ℤ) = 7 * a (m + 7) - 21 * a (m + 6) + 35 * a (m + 5) - 35 * a (m + 4) + 21 * a (m + 3) - 7 * a (m + 2) + a (m + 1) := by
  have h : ∑ i : Fin 64, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_all (m + 1) i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 64, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 64, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    have h0 := hsum 0; rwa [add_zero] at h0
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
lemma a_1 : a 1 = 543 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 1 i = 543
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 2457 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 2 i = 2457
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 8037 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 3 i = 8037
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 21436 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 4 i = 21436
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 49599 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 5 i = 49599
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 103293 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 6 i = 103293
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 198297 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 7 i = 198297
  simp only [v_7]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (2 / 9 : ℚ) * (n : ℚ) ^ 6 + (47 / 12 : ℚ) * (n : ℚ) ^ 5 + (953 / 36 : ℚ) * (n : ℚ) ^ 4 + (1141 / 12 : ℚ) * (n : ℚ) ^ 3 + (6527 / 36 : ℚ) * (n : ℚ) ^ 2 + 172 * n + 64

theorem main_proof_ours :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 / 9 : ℚ) * (n : ℚ) ^ 6 + (47 / 12 : ℚ) * (n : ℚ) ^ 5 + (953 / 36 : ℚ) * (n : ℚ) ^ 4 + (1141 / 12 : ℚ) * (n : ℚ) ^ 3 + (6527 / 36 : ℚ) * (n : ℚ) ^ 2 + 172 * n + 64) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 7) =
      X * (543 - 1344 * X + 2241 * X ^ 2 - 2231 * X ^ 3 + 1334 * X ^ 4 - 447 * X ^ 5 + 64 * X ^ 6)) ∧
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  have hrec : (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simpa using a_rec_ge m
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 7) =
      X * (543 - 1344 * X + 2241 * X ^ 2 - 2231 * X ^ 3 + 1334 * X ^ 4 - 447 * X ^ 5 + 64 * X ^ 6)) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 7) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (21 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (35 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (35 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (21 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        + C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 7) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (543 - 1344 * X + 2241 * X ^ 2 - 2231 * X ^ 3 + 1334 * X ^ 4 - 447 * X ^ 5 + 64 * X ^ 6) : PowerSeries ℚ) =
        C (543 : ℚ) * X ^ 1
        - C (1344 : ℚ) * X ^ 2
        + C (2241 : ℚ) * X ^ 3
        - C (2231 : ℚ) * X ^ 4
        + C (1334 : ℚ) * X ^ 5
        - C (447 : ℚ) * X ^ 6
        + C (64 : ℚ) * X ^ 7 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> try norm_num
    · have hq : (a n : ℚ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
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
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 / 9 : ℚ) * (n : ℚ) ^ 6 + (47 / 12 : ℚ) * (n : ℚ) ^ 5 + (953 / 36 : ℚ) * (n : ℚ) ^ 4 + (1141 / 12 : ℚ) * (n : ℚ) ^ 3 + (6527 / 36 : ℚ) * (n : ℚ) ^ 2 + 172 * n + 64 := by
    have hb_1 : (a 1 : ℚ) = cf 1 := by
      rw [a_1]; unfold cf; push_cast; norm_num
    have hb_2 : (a 2 : ℚ) = cf 2 := by
      rw [a_2]; unfold cf; push_cast; norm_num
    have hb_3 : (a 3 : ℚ) = cf 3 := by
      rw [a_3]; unfold cf; push_cast; norm_num
    have hb_4 : (a 4 : ℚ) = cf 4 := by
      rw [a_4]; unfold cf; push_cast; norm_num
    have hb_5 : (a 5 : ℚ) = cf 5 := by
      rw [a_5]; unfold cf; push_cast; norm_num
    have hb_6 : (a 6 : ℚ) = cf 6 := by
      rw [a_6]; unfold cf; push_cast; norm_num
    have hb_7 : (a 7 : ℚ) = cf 7 := by
      rw [a_7]; unfold cf; push_cast; norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 8) = 7 * cf (m + 7) - 21 * cf (m + 6) + 35 * cf (m + 5) - 35 * cf (m + 4) + 21 * cf (m + 3) - 7 * cf (m + 2) + cf (m + 1) := by
      intro m; unfold cf; push_cast; ring
    have hQ : ∀ m : ℕ,
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
        have hr : (a (m + 8) : ℚ) = 7 * a (m + 7) - 21 * a (m + 6) + 35 * a (m + 5) - 35 * a (m + 4) + 21 * a (m + 3) - 7 * a (m + 2) + a (m + 1) := by
          have h0' := hrec (m + 8) (by omega)
          simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h6, h5, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hQ (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hcf, hgf, hrec⟩


lemma blk : ∀ p q r s : Fin 4, OMA.S_oeis_a250854.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250854.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250854.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250854.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold OMA.S_oeis_a250854.Good isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250854.main := by
  obtain ⟨hcf, _, hrec⟩ := main_proof_ours
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250854.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq 0]; exact a_1
  · rw [a_eq 1]; exact a_2
  · rw [a_eq 2]; exact a_3
  · rw [a_eq 3]; exact a_4
  · rw [a_eq 4]; exact a_5
  · rw [a_eq 5]; exact a_6
  · rw [a_eq 6]; exact a_7
  · intro n hn
    rw [hA (n + 7) (by omega), hA (n + 6) (by omega), hA (n + 5) (by omega), hA (n + 4) (by omega), hA (n + 3) (by omega), hA (n + 2) (by omega), hA (n + 1) (by omega), hA n (by omega)]
    have h := hrec (n + 7) (by omega)
    simp only [show n + 7 - 1 = n + 6 by omega, show n + 7 - 2 = n + 5 by omega, show n + 7 - 3 = n + 4 by omega, show n + 7 - 4 = n + 3 by omega, show n + 7 - 5 = n + 2 by omega, show n + 7 - 6 = n + 1 by omega, show n + 7 - 7 = n by omega] at h
    exact h
  · intro n hn
    rw [hA n hn, ← Int.cast_inj (α := ℚ)]
    push_cast
    rw [hcf n hn]
    ring

end OMA.P250854

theorem OMA.solution : type_of% @OMA.S_oeis_a250854.main := OMA.P250854.main_proof
