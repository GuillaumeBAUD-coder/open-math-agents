import OMAStatements.S_oeis_a250814

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence and closed form bridged to upstream Blk/Good encoding.

namespace OMA.P250814

open PowerSeries

/-- A `2 X 2` `0..2` subblock `(a, b / c, d)` has `b - a ≤ d - c` (in `ℤ`) and `min a c ≤ min b d`. -/
def okBlock (a b c d : Fin 3) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ min a.val c.val ≤ min b.val d.val

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- A `3 X (m + 1)` `0..2` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin 3 → Fin (m + 1) → Fin 3) : Prop :=
  ∀ i : Fin 2, ∀ j : Fin m,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin 3 → Fin (m + 1) → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250814: Number of (2+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250814 PowerSeries

abbrev Col := Fin 3 → Fin 3

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

def enc (c : Col) : Fin 27 :=
  ⟨9 * (c 0).val + 3 * (c 1).val + (c 2).val, by
    have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; omega⟩

def dec (k : Fin 27) : Col := fun r =>
  have hk := k.isLt
  if r.val = 0 then ⟨k.val / 9, by omega⟩
  else if r.val = 1 then ⟨(k.val / 3) % 3, by omega⟩
  else ⟨k.val % 3, by omega⟩

lemma enc_dec : ∀ k : Fin 27, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ c : Col, dec (enc c) = c := by
  intro c; ext r
  have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt
  fin_cases r
  · change (dec (enc c) 0).val = (c 0).val; simp [dec, enc]; try omega
  · change (dec (enc c) 1).val = (c 1).val; simp [dec, enc]; try omega
  · change (dec (enc c) 2).val = (c 2).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 27) : Prop := okCol (dec i) (dec j)

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
  | 9 => 79851319
  | 10 => 8408102
  | 11 => 2052
  | 12 => 100888576
  | 13 => 67264512
  | 14 => 16384
  | 15 => 229376
  | 16 => 196608
  | 17 => 131072
  | 18 => 81686327
  | 19 => 9980966
  | 20 => 1050628
  | 21 => 115568640
  | 22 => 79847424
  | 23 => 8404992
  | 24 => 117440512
  | 25 => 100663296
  | 26 => 67108864
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 27, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 27 → ℕ) (i : Fin 27) : ℕ :=
  ∑ j : Fin 27, if ok2 i j then f j else 0

def v : ℕ → Fin 27 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Col) → ℕ) :
    ∑ x, f x = ∑ c : Col, ∑ y : Fin (m + 1) → Col, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Col) → ℕ) :
    ∑ y, g y = ∑ i : Fin 27, ∑ y : Fin (m + 1) → Col, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Col, ∑ i : Fin 27, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 27) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 27, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [← (Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 2)) => Fin 3)).symm.sum_comp]
  have htr : ∀ y : Fin (n + 2) → Col,
      isValid (n + 1) ((Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 2)) => Fin 3)).symm y) ↔
      isValidT (n + 1) y := fun y => isValid_transpose (n + 1) y
  simp only [htr]
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
  | 9 => 15
  | 10 => 7
  | 11 => 2
  | 12 => 7
  | 13 => 4
  | 14 => 1
  | 15 => 3
  | 16 => 2
  | 17 => 1
  | 18 => 18
  | 19 => 9
  | 20 => 3
  | 21 => 10
  | 22 => 6
  | 23 => 2
  | 24 => 3
  | 25 => 2
  | 26 => 1
  | _ => 0
def vtab2 (i : Fin 27) : ℕ := match i.val with
  | 0 => 28
  | 1 => 7
  | 2 => 1
  | 3 => 18
  | 4 => 7
  | 5 => 1
  | 6 => 6
  | 7 => 3
  | 8 => 1
  | 9 => 60
  | 10 => 18
  | 11 => 3
  | 12 => 18
  | 13 => 7
  | 14 => 1
  | 15 => 6
  | 16 => 3
  | 17 => 1
  | 18 => 90
  | 19 => 30
  | 20 => 6
  | 21 => 36
  | 22 => 15
  | 23 => 3
  | 24 => 6
  | 25 => 3
  | 26 => 1
  | _ => 0
def vtab3 (i : Fin 27) : ℕ := match i.val with
  | 0 => 55
  | 1 => 10
  | 2 => 1
  | 3 => 34
  | 4 => 10
  | 5 => 1
  | 6 => 10
  | 7 => 4
  | 8 => 1
  | 9 => 154
  | 10 => 34
  | 11 => 4
  | 12 => 34
  | 13 => 10
  | 14 => 1
  | 15 => 10
  | 16 => 4
  | 17 => 1
  | 18 => 280
  | 19 => 70
  | 20 => 10
  | 21 => 88
  | 22 => 28
  | 23 => 4
  | 24 => 10
  | 25 => 4
  | 26 => 1
  | _ => 0
def vtab4 (i : Fin 27) : ℕ := match i.val with
  | 0 => 91
  | 1 => 13
  | 2 => 1
  | 3 => 55
  | 4 => 13
  | 5 => 1
  | 6 => 15
  | 7 => 5
  | 8 => 1
  | 9 => 315
  | 10 => 55
  | 11 => 5
  | 12 => 55
  | 13 => 13
  | 14 => 1
  | 15 => 15
  | 16 => 5
  | 17 => 1
  | 18 => 675
  | 19 => 135
  | 20 => 15
  | 21 => 175
  | 22 => 45
  | 23 => 5
  | 24 => 15
  | 25 => 5
  | 26 => 1
  | _ => 0
def vtab5 (i : Fin 27) : ℕ := match i.val with
  | 0 => 136
  | 1 => 16
  | 2 => 1
  | 3 => 81
  | 4 => 16
  | 5 => 1
  | 6 => 21
  | 7 => 6
  | 8 => 1
  | 9 => 561
  | 10 => 81
  | 11 => 6
  | 12 => 81
  | 13 => 16
  | 14 => 1
  | 15 => 21
  | 16 => 6
  | 17 => 1
  | 18 => 1386
  | 19 => 231
  | 20 => 21
  | 21 => 306
  | 22 => 66
  | 23 => 6
  | 24 => 21
  | 25 => 6
  | 26 => 1
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

def err (m : ℕ) (i : Fin 27) : ℤ :=
  (v (m + 5) i : ℤ) - 5 * (v (m + 4) i : ℤ) + 10 * (v (m + 3) i : ℤ) - 10 * (v (m + 2) i : ℤ) + 5 * (v (m + 1) i : ℤ) - (v m i : ℤ)

lemma err_base : ∀ i : Fin 27, err 0 i = 0 := by
  intro i
  change (v 5 i : ℤ) - 5 * (v 4 i : ℤ) + 10 * (v 3 i : ℤ) - 10 * (v 2 i : ℤ) + 5 * (v 1 i : ℤ) - (v 0 i : ℤ) = 0
  simp only [v_5, v_4, v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 27) :
    err (m + 1) i = ∑ j : Fin 27, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 27, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step, Nat.cast_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> rfl
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 27) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 6) : ℤ) = 5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3) - 5 * a (m + 2) + a (m + 1) := by
  have h : ∑ i : Fin 27, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_all (m + 1) i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 27, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 27, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    have h0 := hsum 0; rwa [add_zero] at h0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  have h2_5 : m + 1 + 5 = m + 6 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 129 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 1 i = 129
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 379 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 2 i = 379
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 873 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 3 i = 873
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 1731 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 4 i = 1731
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 3097 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 27, v 5 i = 3097
  simp only [v_5]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (n : ℚ) ^ 4 + 10 * (n : ℚ) ^ 3 + 37 * (n : ℚ) ^ 2 + 54 * n + 27

theorem main_proof_ours :
    (∀ n : ℕ, 1 ≤ n → a n = n ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5) =
      X * (129 - 266 * X + 268 * X ^ 2 - 134 * X ^ 3 + 27 * X ^ 4)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  have hrec : (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simpa using a_rec_ge m
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5) =
      X * (129 - 266 * X + 268 * X ^ 2 - 134 * X ^ 3 + 27 * X ^ 4)) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (129 - 266 * X + 268 * X ^ 2 - 134 * X ^ 3 + 27 * X ^ 4) : PowerSeries ℚ) =
        C (129 : ℚ) * X ^ 1
        - C (266 : ℚ) * X ^ 2
        + C (268 : ℚ) * X ^ 3
        - C (134 : ℚ) * X ^ 4
        + C (27 : ℚ) * X ^ 5 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5] <;> try norm_num
    · have hq : (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
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
  have hcf : ∀ n : ℕ, 1 ≤ n → a n = n ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 := by
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
    have cf_rec : ∀ m : ℕ, cf (m + 6) = 5 * cf (m + 5) - 10 * cf (m + 4) + 10 * cf (m + 3) - 5 * cf (m + 2) + cf (m + 1) := by
      intro m; unfold cf; push_cast; ring
    have hQ : ∀ m : ℕ,
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
        have hr : (a (m + 6) : ℚ) = 5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3) - 5 * a (m + 2) + a (m + 1) := by
          have h0' := hrec (m + 6) (by omega)
          simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hQ (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    unfold cf at h
    have hcast : ((a n : ℕ) : ℚ) = ((n ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℕ) : ℚ) := by
      push_cast; exact h
    exact Nat.cast_injective hcast
  exact ⟨hcf, hgf, hrec⟩


lemma blk : ∀ p q r s : Fin 3, OMA.S_oeis_a250814.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250814.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250814.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250814.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold OMA.S_oeis_a250814.Good isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250814.main := by
  obtain ⟨hcf, _, hrec⟩ := main_proof_ours
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250814.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq 0]; exact a_1
  · rw [a_eq 1]; exact a_2
  · rw [a_eq 2]; exact a_3
  · rw [a_eq 3]; exact a_4
  · rw [a_eq 4]; exact a_5
  · intro n hn
    rw [hA (n + 5) (by omega), hA (n + 4) (by omega), hA (n + 3) (by omega), hA (n + 2) (by omega), hA (n + 1) (by omega), hA n (by omega)]
    have h := hrec (n + 5) (by omega)
    simp only [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega, show n + 5 - 4 = n + 1 by omega, show n + 5 - 5 = n by omega] at h
    exact h
  · intro n hn
    rw [hA n hn, hcf n hn]
    push_cast
    ring

end OMA.P250814

theorem OMA.solution : type_of% @OMA.S_oeis_a250814.main := OMA.P250814.main_proof
