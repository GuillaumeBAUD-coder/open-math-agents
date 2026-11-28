import OMAStatements.S_oeis_a250659

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence, g.f. and closed form bridged to upstream CellOK encoding.

namespace OMA.P250659

open PowerSeries

/-- A `2 X 2` `0..1` subblock `(a, b / c, d)` has `b - a ≤ d - c` (in `ℤ`) and `min a c ≤ min b d`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ min a.val c.val ≤ min b.val d.val

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- A `6 X (m + 1)` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin 6 → Fin (m + 1) → Fin 2) : Prop :=
  ∀ i : Fin 5, ∀ j : Fin m,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin 6 → Fin (m + 1) → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250659: Number of (5+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250659 PowerSeries

abbrev Col := Fin 6 → Fin 2

def okCol (c₁ c₂ : Col) : Prop :=
  ∀ i : Fin 5, okBlock (c₁ i.castSucc) (c₂ i.castSucc) (c₁ i.succ) (c₂ i.succ)

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
  ⟨32 * (c 0).val + 16 * (c 1).val + 8 * (c 2).val + 4 * (c 3).val + 2 * (c 4).val + (c 5).val, by
    have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; have h3 := (c 3).isLt; have h4 := (c 4).isLt; have h5 := (c 5).isLt; omega⟩

def dec (k : Fin 64) : Col := fun r =>
  have hk := k.isLt
  if r.val = 0 then ⟨k.val / 32, by omega⟩
  else if r.val = 1 then ⟨(k.val / 16) % 2, by omega⟩
  else if r.val = 2 then ⟨(k.val / 8) % 2, by omega⟩
  else if r.val = 3 then ⟨(k.val / 4) % 2, by omega⟩
  else if r.val = 4 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 64, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ c : Col, dec (enc c) = c := by
  intro c; ext r
  have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; have h3 := (c 3).isLt; have h4 := (c 4).isLt; have h5 := (c 5).isLt
  fin_cases r
  · change (dec (enc c) 0).val = (c 0).val; simp [dec, enc]; try omega
  · change (dec (enc c) 1).val = (c 1).val; simp [dec, enc]; try omega
  · change (dec (enc c) 2).val = (c 2).val; simp [dec, enc]; try omega
  · change (dec (enc c) 3).val = (c 3).val; simp [dec, enc]; try omega
  · change (dec (enc c) 4).val = (c 4).val; simp [dec, enc]; try omega
  · change (dec (enc c) 5).val = (c 5).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 64) : Prop := okCol (dec i) (dec j)

instance (i j : Fin 64) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 64) : ℕ := match i.val with
  | 0 => 9223372039002292363
  | 1 => 2
  | 2 => 12
  | 3 => 8
  | 4 => 176
  | 5 => 32
  | 6 => 192
  | 7 => 128
  | 8 => 35584
  | 9 => 512
  | 10 => 3072
  | 11 => 2048
  | 12 => 45056
  | 13 => 8192
  | 14 => 49152
  | 15 => 32768
  | 16 => 2156593152
  | 17 => 131072
  | 18 => 786432
  | 19 => 524288
  | 20 => 11534336
  | 21 => 2097152
  | 22 => 12582912
  | 23 => 8388608
  | 24 => 2332033024
  | 25 => 33554432
  | 26 => 201326592
  | 27 => 134217728
  | 28 => 2952790016
  | 29 => 536870912
  | 30 => 3221225472
  | 31 => 2147483648
  | 32 => 9223513373491101835
  | 33 => 8589934594
  | 34 => 51539607564
  | 35 => 34359738376
  | 36 => 755914244272
  | 37 => 137438953504
  | 38 => 824633721024
  | 39 => 549755814016
  | 40 => 152832116296448
  | 41 => 2199023256064
  | 42 => 13194139536384
  | 43 => 8796093024256
  | 44 => 193514046533632
  | 45 => 35184372097024
  | 46 => 211106232582144
  | 47 => 140737488388096
  | 48 => 9262497058617556992
  | 49 => 562949953421312
  | 50 => 3377699720527872
  | 51 => 2251799813685248
  | 52 => 49539595901075456
  | 53 => 9007199254740992
  | 54 => 54043195528445952
  | 55 => 36028797018963968
  | 56 => 10016005571271983104
  | 57 => 144115188075855872
  | 58 => 864691128455135232
  | 59 => 576460752303423488
  | 60 => 12682136550675316736
  | 61 => 2305843009213693952
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
  rw [← (Equiv.piComm (fun (_ : Fin 6) (_ : Fin (n + 2)) => Fin 2)).symm.sum_comp]
  have htr : ∀ y : Fin (n + 2) → Col,
      isValid (n + 1) ((Equiv.piComm (fun (_ : Fin 6) (_ : Fin (n + 2)) => Fin 2)).symm y) ↔
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
  | 0 => 7
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | 6 => 2
  | 7 => 1
  | 8 => 4
  | 9 => 1
  | 10 => 2
  | 11 => 1
  | 12 => 3
  | 13 => 1
  | 14 => 2
  | 15 => 1
  | 16 => 5
  | 17 => 1
  | 18 => 2
  | 19 => 1
  | 20 => 3
  | 21 => 1
  | 22 => 2
  | 23 => 1
  | 24 => 4
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 3
  | 29 => 1
  | 30 => 2
  | 31 => 1
  | 32 => 12
  | 33 => 2
  | 34 => 4
  | 35 => 2
  | 36 => 6
  | 37 => 2
  | 38 => 4
  | 39 => 2
  | 40 => 8
  | 41 => 2
  | 42 => 4
  | 43 => 2
  | 44 => 6
  | 45 => 2
  | 46 => 4
  | 47 => 2
  | 48 => 5
  | 49 => 1
  | 50 => 2
  | 51 => 1
  | 52 => 3
  | 53 => 1
  | 54 => 2
  | 55 => 1
  | 56 => 4
  | 57 => 1
  | 58 => 2
  | 59 => 1
  | 60 => 3
  | 61 => 1
  | 62 => 2
  | 63 => 1
  | _ => 0
def vtab2 (i : Fin 64) : ℕ := match i.val with
  | 0 => 13
  | 1 => 1
  | 2 => 3
  | 3 => 1
  | 4 => 5
  | 5 => 1
  | 6 => 3
  | 7 => 1
  | 8 => 7
  | 9 => 1
  | 10 => 3
  | 11 => 1
  | 12 => 5
  | 13 => 1
  | 14 => 3
  | 15 => 1
  | 16 => 9
  | 17 => 1
  | 18 => 3
  | 19 => 1
  | 20 => 5
  | 21 => 1
  | 22 => 3
  | 23 => 1
  | 24 => 7
  | 25 => 1
  | 26 => 3
  | 27 => 1
  | 28 => 5
  | 29 => 1
  | 30 => 3
  | 31 => 1
  | 32 => 33
  | 33 => 3
  | 34 => 9
  | 35 => 3
  | 36 => 15
  | 37 => 3
  | 38 => 9
  | 39 => 3
  | 40 => 21
  | 41 => 3
  | 42 => 9
  | 43 => 3
  | 44 => 15
  | 45 => 3
  | 46 => 9
  | 47 => 3
  | 48 => 9
  | 49 => 1
  | 50 => 3
  | 51 => 1
  | 52 => 5
  | 53 => 1
  | 54 => 3
  | 55 => 1
  | 56 => 7
  | 57 => 1
  | 58 => 3
  | 59 => 1
  | 60 => 5
  | 61 => 1
  | 62 => 3
  | 63 => 1
  | _ => 0
def vtab3 (i : Fin 64) : ℕ := match i.val with
  | 0 => 19
  | 1 => 1
  | 2 => 4
  | 3 => 1
  | 4 => 7
  | 5 => 1
  | 6 => 4
  | 7 => 1
  | 8 => 10
  | 9 => 1
  | 10 => 4
  | 11 => 1
  | 12 => 7
  | 13 => 1
  | 14 => 4
  | 15 => 1
  | 16 => 13
  | 17 => 1
  | 18 => 4
  | 19 => 1
  | 20 => 7
  | 21 => 1
  | 22 => 4
  | 23 => 1
  | 24 => 10
  | 25 => 1
  | 26 => 4
  | 27 => 1
  | 28 => 7
  | 29 => 1
  | 30 => 4
  | 31 => 1
  | 32 => 64
  | 33 => 4
  | 34 => 16
  | 35 => 4
  | 36 => 28
  | 37 => 4
  | 38 => 16
  | 39 => 4
  | 40 => 40
  | 41 => 4
  | 42 => 16
  | 43 => 4
  | 44 => 28
  | 45 => 4
  | 46 => 16
  | 47 => 4
  | 48 => 13
  | 49 => 1
  | 50 => 4
  | 51 => 1
  | 52 => 7
  | 53 => 1
  | 54 => 4
  | 55 => 1
  | 56 => 10
  | 57 => 1
  | 58 => 4
  | 59 => 1
  | 60 => 7
  | 61 => 1
  | 62 => 4
  | 63 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 64, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 64, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 64, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 64, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 64) : ℤ :=
  (v (m + 3) i : ℤ) - 3 * (v (m + 2) i : ℤ) + 3 * (v (m + 1) i : ℤ) - (v m i : ℤ)

lemma err_base : ∀ i : Fin 64, err 0 i = 0 := by
  intro i
  change (v 3 i : ℤ) - 3 * (v 2 i : ℤ) + 3 * (v 1 i : ℤ) - (v 0 i : ℤ) = 0
  simp only [v_3, v_2, v_1, v_0]
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
    (a (m + 4) : ℤ) = 3 * a (m + 3) - 3 * a (m + 2) + a (m + 1) := by
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
  simp only [h2_1, h2_2, h2_3] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 159 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 1 i = 159
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 286 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 2 i = 286
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 445 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 64, v 3 i = 445
  simp only [v_3]; decide +kernel

def cf (n : ℕ) : ℚ :=
  16 * (n : ℚ) ^ 2 + 79 * n + 64

theorem main_proof_ours :
    (∀ n : ℕ, 1 ≤ n → a n = 16 * n ^ 2 + 79 * n + 64) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3) =
      X * (159 - 191 * X + 64 * X ^ 2)) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  have hrec : (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using a_rec_ge m
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3) =
      X * (159 - 191 * X + 64 * X ^ 2)) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (159 - 191 * X + 64 * X ^ 2) : PowerSeries ℚ) =
        C (159 : ℚ) * X ^ 1
        - C (191 : ℚ) * X ^ 2
        + C (64 : ℚ) * X ^ 3 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3] <;> try norm_num
    · have hq : (a n : ℚ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      simp only [c1, c2, c3, e1, e2, e3, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → a n = 16 * n ^ 2 + 79 * n + 64 := by
    have hb_1 : (a 1 : ℚ) = cf 1 := by
      rw [a_1]; unfold cf; push_cast; norm_num
    have hb_2 : (a 2 : ℚ) = cf 2 := by
      rw [a_2]; unfold cf; push_cast; norm_num
    have hb_3 : (a 3 : ℚ) = cf 3 := by
      rw [a_3]; unfold cf; push_cast; norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 4) = 3 * cf (m + 3) - 3 * cf (m + 2) + cf (m + 1) := by
      intro m; unfold cf; push_cast; ring
    have hQ : ∀ m : ℕ,
        (a (m + 1) : ℚ) = cf (m + 1) ∧
        (a (m + 2) : ℚ) = cf (m + 2) ∧
        (a (m + 3) : ℚ) = cf (m + 3) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_1, hb_2, hb_3⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), ?_⟩
        rw [show m + 1 + 3 = m + 4 by omega]
        have hr : (a (m + 4) : ℚ) = 3 * a (m + 3) - 3 * a (m + 2) + a (m + 1) := by
          have h0' := hrec (m + 4) (by omega)
          simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hQ (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    unfold cf at h
    have hcast : ((a n : ℕ) : ℚ) = ((16 * n ^ 2 + 79 * n + 64 : ℕ) : ℚ) := by
      push_cast; exact h
    exact Nat.cast_injective hcast
  exact ⟨hcf, hgf, hrec⟩


lemma blk : ∀ p q r s : Fin 2,
    OMA.S_oeis_a250659.CellOK ((p : ℕ) : ℤ) ((q : ℕ) : ℤ) ((r : ℕ) : ℤ) ((s : ℕ) : ℤ) ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250659.CellOK, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250659.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250659.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250659.main := by
  obtain ⟨hcf, hgf, hrec⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250659.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250659.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega)]
    exact hrec n (by omega)
  · rw [hser, OMA.S_oeis_a250659.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n (by omega), hcf n (by omega)]
    push_cast
    ring

end OMA.P250659

theorem OMA.solution : type_of% @OMA.S_oeis_a250659.main := OMA.P250659.main_proof
