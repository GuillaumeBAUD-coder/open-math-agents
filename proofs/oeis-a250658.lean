import OMAStatements.S_oeis_a250658

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence and closed form bridged to upstream Blk/Good encoding.

namespace OMA.P250658

open PowerSeries

/-- A `2 X 2` `0..1` subblock `(a, b / c, d)` has `b - a ≤ d - c` (in `ℤ`) and `min a c ≤ min b d`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ min a.val c.val ≤ min b.val d.val

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- A `5 X (m + 1)` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin 5 → Fin (m + 1) → Fin 2) : Prop :=
  ∀ i : Fin 4, ∀ j : Fin m,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin 5 → Fin (m + 1) → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250658: Number of (4+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250658 PowerSeries

abbrev Col := Fin 5 → Fin 2

def okCol (c₁ c₂ : Col) : Prop :=
  ∀ i : Fin 4, okBlock (c₁ i.castSucc) (c₂ i.castSucc) (c₁ i.succ) (c₂ i.succ)

instance (c₁ c₂ : Col) : Decidable (okCol c₁ c₂) := by
  unfold okCol; infer_instance

def isValidT (m : ℕ) (y : Fin (m + 1) → Col) : Prop :=
  ∀ j : Fin m, okCol (y j.castSucc) (y j.succ)

instance (m : ℕ) (y : Fin (m + 1) → Col) : Decidable (isValidT m y) := by
  unfold isValidT; infer_instance

lemma isValid_transpose (m : ℕ) (y : Fin (m + 1) → Col) :
    isValid m (fun i j => y j i) ↔ isValidT m y :=
  forall_comm

def enc (c : Col) : Fin 32 :=
  ⟨16 * (c 0).val + 8 * (c 1).val + 4 * (c 2).val + 2 * (c 3).val + (c 4).val, by
    have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; have h3 := (c 3).isLt; have h4 := (c 4).isLt; omega⟩

def dec (k : Fin 32) : Col := fun r =>
  have hk := k.isLt
  if r.val = 0 then ⟨k.val / 16, by omega⟩
  else if r.val = 1 then ⟨(k.val / 8) % 2, by omega⟩
  else if r.val = 2 then ⟨(k.val / 4) % 2, by omega⟩
  else if r.val = 3 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 32, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ c : Col, dec (enc c) = c := by
  intro c; ext r
  have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; have h3 := (c 3).isLt; have h4 := (c 4).isLt
  fin_cases r
  · change (dec (enc c) 0).val = (c 0).val; simp [dec, enc]; try omega
  · change (dec (enc c) 1).val = (c 1).val; simp [dec, enc]; try omega
  · change (dec (enc c) 2).val = (c 2).val; simp [dec, enc]; try omega
  · change (dec (enc c) 3).val = (c 3).val; simp [dec, enc]; try omega
  · change (dec (enc c) 4).val = (c 4).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 32) : Prop := okCol (dec i) (dec j)

instance (i j : Fin 32) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 32) : ℕ := match i.val with
  | 0 => 2147516555
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
  | 16 => 2156626059
  | 17 => 131074
  | 18 => 786444
  | 19 => 524296
  | 20 => 11534512
  | 21 => 2097184
  | 22 => 12583104
  | 23 => 8388736
  | 24 => 2332033024
  | 25 => 33554432
  | 26 => 201326592
  | 27 => 134217728
  | 28 => 2952790016
  | 29 => 536870912
  | 30 => 3221225472
  | 31 => 2147483648
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 32, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 32 → ℕ) (i : Fin 32) : ℕ :=
  ∑ j : Fin 32, if ok2 i j then f j else 0

def v : ℕ → Fin 32 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Col) → ℕ) :
    ∑ x, f x = ∑ c : Col, ∑ y : Fin (m + 1) → Col, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Col) → ℕ) :
    ∑ y, g y = ∑ i : Fin 32, ∑ y : Fin (m + 1) → Col, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Col, ∑ i : Fin 32, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 32) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 32, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [← (Equiv.piComm (fun (_ : Fin 5) (_ : Fin (n + 2)) => Fin 2)).symm.sum_comp]
  have htr : ∀ y : Fin (n + 2) → Col,
      isValid (n + 1) ((Equiv.piComm (fun (_ : Fin 5) (_ : Fin (n + 2)) => Fin 2)).symm y) ↔
      isValidT (n + 1) y := fun y => isValid_transpose (n + 1) y
  simp only [htr]
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
  | 16 => 10
  | 17 => 2
  | 18 => 4
  | 19 => 2
  | 20 => 6
  | 21 => 2
  | 22 => 4
  | 23 => 2
  | 24 => 4
  | 25 => 1
  | 26 => 2
  | 27 => 1
  | 28 => 3
  | 29 => 1
  | 30 => 2
  | 31 => 1
  | _ => 0
def vtab2 (i : Fin 32) : ℕ := match i.val with
  | 0 => 11
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
  | 16 => 27
  | 17 => 3
  | 18 => 9
  | 19 => 3
  | 20 => 15
  | 21 => 3
  | 22 => 9
  | 23 => 3
  | 24 => 7
  | 25 => 1
  | 26 => 3
  | 27 => 1
  | 28 => 5
  | 29 => 1
  | 30 => 3
  | 31 => 1
  | _ => 0
def vtab3 (i : Fin 32) : ℕ := match i.val with
  | 0 => 16
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
  | 16 => 52
  | 17 => 4
  | 18 => 16
  | 19 => 4
  | 20 => 28
  | 21 => 4
  | 22 => 16
  | 23 => 4
  | 24 => 10
  | 25 => 1
  | 26 => 4
  | 27 => 1
  | 28 => 7
  | 29 => 1
  | 30 => 4
  | 31 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 32, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 32, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 32, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 32, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 32) : ℤ :=
  (v (m + 3) i : ℤ) - 3 * (v (m + 2) i : ℤ) + 3 * (v (m + 1) i : ℤ) - (v m i : ℤ)

lemma err_base : ∀ i : Fin 32, err 0 i = 0 := by
  intro i
  change (v 3 i : ℤ) - 3 * (v 2 i : ℤ) + 3 * (v 1 i : ℤ) - (v 0 i : ℤ) = 0
  simp only [v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 32) :
    err (m + 1) i = ∑ j : Fin 32, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 32, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step, Nat.cast_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> rfl
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 32) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 4) : ℤ) = 3 * a (m + 3) - 3 * a (m + 2) + a (m + 1) := by
  have h : ∑ i : Fin 32, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_all (m + 1) i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 32, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 32, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    have h0 := hsum 0; rwa [add_zero] at h0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  simp only [h2_1, h2_2, h2_3] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 79 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 1 i = 79
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 142 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 2 i = 142
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 221 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 32, v 3 i = 221
  simp only [v_3]; decide +kernel

def cf (n : ℕ) : ℚ :=
  8 * (n : ℚ) ^ 2 + 39 * n + 32

theorem main_proof_ours :
    (∀ n : ℕ, 1 ≤ n → a n = 8 * n ^ 2 + 39 * n + 32) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3) =
      X * (79 - 95 * X + 32 * X ^ 2)) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  have hrec : (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using a_rec_ge m
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3) =
      X * (79 - 95 * X + 32 * X ^ 2)) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (79 - 95 * X + 32 * X ^ 2) : PowerSeries ℚ) =
        C (79 : ℚ) * X ^ 1
        - C (95 : ℚ) * X ^ 2
        + C (32 : ℚ) * X ^ 3 := by
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
  have hcf : ∀ n : ℕ, 1 ≤ n → a n = 8 * n ^ 2 + 39 * n + 32 := by
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
    have hcast : ((a n : ℕ) : ℚ) = ((8 * n ^ 2 + 39 * n + 32 : ℕ) : ℚ) := by
      push_cast; exact h
    exact Nat.cast_injective hcast
  exact ⟨hcf, hgf, hrec⟩


lemma blk : ∀ p q r s : Fin 2, OMA.S_oeis_a250658.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250658.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250658.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250658.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold OMA.S_oeis_a250658.Good isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250658.main := by
  obtain ⟨hcf, _, hrec⟩ := main_proof_ours
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250658.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq 0]; exact a_1
  · rw [a_eq 1]; exact a_2
  · rw [a_eq 2]; exact a_3
  · intro n hn
    rw [hA (n + 3) (by omega), hA (n + 2) (by omega), hA (n + 1) (by omega), hA n (by omega)]
    have h := hrec (n + 3) (by omega)
    simp only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega, show n + 3 - 3 = n by omega] at h
    exact h
  · intro n hn
    rw [hA n hn, hcf n hn]
    push_cast
    ring

end OMA.P250658

theorem OMA.solution : type_of% @OMA.S_oeis_a250658.main := OMA.P250658.main_proof
