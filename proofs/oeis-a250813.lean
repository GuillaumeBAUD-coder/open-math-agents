import OMAStatements.S_oeis_a250813

-- Credit: @Dariusthedoggie
-- Proof: column transfer matrix annihilated by the quintic recurrence polynomial, giving recurrence, g.f. and closed form, bridged to the transposed Nat.card encoding.

namespace OMA.P250813

open PowerSeries
/-- A `2 X 2` `0..2` subblock `(a, b / c, d)` has `b - a ≤ d - c` (in `ℤ`) and `min a c ≤ min b d`. -/
def okBlock (a b c d : Fin 3) : Prop :=
  (b.val : ℤ) - a.val ≤ (d.val : ℤ) - c.val ∧ min a.val c.val ≤ min b.val d.val

instance (a b c d : Fin 3) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- A `2 X (m + 1)` `0..2` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin 2 → Fin (m + 1) → Fin 3) : Prop :=
  ∀ i : Fin 1, ∀ j : Fin m,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin 2 → Fin (m + 1) → Fin 3) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250813: Number of (1+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Col := Fin 2 → Fin 3

def okCol (c₁ c₂ : Col) : Prop :=
  ∀ i : Fin 1, okBlock (c₁ i.castSucc) (c₂ i.castSucc) (c₁ i.succ) (c₂ i.succ)

instance (c₁ c₂ : Col) : Decidable (okCol c₁ c₂) := by
  unfold okCol; infer_instance

def isValidT (m : ℕ) (y : Fin (m + 1) → Col) : Prop :=
  ∀ j : Fin m, okCol (y j.castSucc) (y j.succ)

instance (m : ℕ) (y : Fin (m + 1) → Col) : Decidable (isValidT m y) := by
  unfold isValidT; infer_instance

lemma isValid_transpose (m : ℕ) (y : Fin (m + 1) → Col) :
    isValid m (fun i j => y j i) ↔ isValidT m y :=
  forall_comm

def enc (c : Col) : Fin 9 :=
  ⟨3 * (c 0).val + (c 1).val, by
    have h0 := (c 0).isLt; have h1 := (c 1).isLt; omega⟩

def dec (k : Fin 9) : Col := fun r =>
  have hk := k.isLt
  if r.val = 0 then ⟨k.val / 3, by omega⟩
  else ⟨k.val % 3, by omega⟩

lemma enc_dec : ∀ k : Fin 9, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ c : Col, dec (enc c) = c := by
  intro c; ext r
  have h0 := (c 0).isLt; have h1 := (c 1).isLt
  fin_cases r
  · change (dec (enc c) 0).val = (c 0).val; simp [dec, enc]; try omega
  · change (dec (enc c) 1).val = (c 1).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 9) : Prop := okCol (dec i) (dec j)

instance (i j : Fin 9) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 9) : ℕ := match i.val with
  | 0 => 311
  | 1 => 38
  | 2 => 4
  | 3 => 447
  | 4 => 304
  | 5 => 32
  | 6 => 511
  | 7 => 432
  | 8 => 256
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 9, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 9 → ℕ) (i : Fin 9) : ℕ :=
  ∑ j : Fin 9, if ok2 i j then f j else 0

def v : ℕ → Fin 9 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Col) → ℕ) :
    ∑ x, f x = ∑ c : Col, ∑ y : Fin (m + 1) → Col, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Col) → ℕ) :
    ∑ y, g y = ∑ i : Fin 9, ∑ y : Fin (m + 1) → Col, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Col, ∑ i : Fin 9, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 9) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 9, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [← (Equiv.piComm (fun (_ : Fin 2) (_ : Fin (n + 2)) => Fin 3)).symm.sum_comp]
  have htr : ∀ y : Fin (n + 2) → Col,
      isValid (n + 1) ((Equiv.piComm (fun (_ : Fin 2) (_ : Fin (n + 2)) => Fin 3)).symm y) ↔
      isValidT (n + 1) y := fun y => isValid_transpose (n + 1) y
  simp only [htr]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 9) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | _ => 0
def vtab1 (i : Fin 9) : ℕ := match i.val with
  | 0 => 6
  | 1 => 3
  | 2 => 1
  | 3 => 8
  | 4 => 3
  | 5 => 1
  | 6 => 9
  | 7 => 4
  | 8 => 1
  | _ => 0
def vtab2 (i : Fin 9) : ℕ := match i.val with
  | 0 => 15
  | 1 => 5
  | 2 => 1
  | 3 => 27
  | 4 => 5
  | 5 => 1
  | 6 => 36
  | 7 => 9
  | 8 => 1
  | _ => 0
def vtab3 (i : Fin 9) : ℕ := match i.val with
  | 0 => 28
  | 1 => 7
  | 2 => 1
  | 3 => 64
  | 4 => 7
  | 5 => 1
  | 6 => 100
  | 7 => 16
  | 8 => 1
  | _ => 0
def vtab4 (i : Fin 9) : ℕ := match i.val with
  | 0 => 45
  | 1 => 9
  | 2 => 1
  | 3 => 125
  | 4 => 9
  | 5 => 1
  | 6 => 225
  | 7 => 25
  | 8 => 1
  | _ => 0
def vtab5 (i : Fin 9) : ℕ := match i.val with
  | 0 => 66
  | 1 => 11
  | 2 => 1
  | 3 => 216
  | 4 => 11
  | 5 => 1
  | 6 => 441
  | 7 => 36
  | 8 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 9, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 9, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 9, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 9, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 9, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 9, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 9) : ℤ :=
  (v (m + 5) i : ℤ) - 5 * (v (m + 4) i : ℤ) + 10 * (v (m + 3) i : ℤ) - 10 * (v (m + 2) i : ℤ) + 5 * (v (m + 1) i : ℤ) - (v m i : ℤ)

lemma err_base : ∀ i : Fin 9, err 0 i = 0 := by
  intro i
  change (v 5 i : ℤ) - 5 * (v 4 i : ℤ) + 10 * (v 3 i : ℤ) - 10 * (v 2 i : ℤ) + 5 * (v 1 i : ℤ) - (v 0 i : ℤ) = 0
  simp only [v_5, v_4, v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 9) :
    err (m + 1) i = ∑ j : Fin 9, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 9, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step, Nat.cast_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> rfl
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 9) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 6) : ℤ) = 5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3) - 5 * a (m + 2) + a (m + 1) := by
  have h : ∑ i : Fin 9, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_all (m + 1) i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 9, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 9, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
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
lemma a_1 : a 1 = 36 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 1 i = 36
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 100 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 2 i = 100
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 225 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 3 i = 225
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 441 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 4 i = 441
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 784 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 5 i = 784
  simp only [v_5]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (1 / 4 : ℚ) * (n : ℚ) ^ 4 + (5 / 2 : ℚ) * (n : ℚ) ^ 3 + (37 / 4 : ℚ) * (n : ℚ) ^ 2 + 15 * n + 9

theorem main_proof_ours :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 4 : ℚ) * (n : ℚ) ^ 4 + (5 / 2 : ℚ) * (n : ℚ) ^ 3 + (37 / 4 : ℚ) * (n : ℚ) ^ 2 + 15 * n + 9) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5) =
      X * (36 - 80 * X + 85 * X ^ 2 - 44 * X ^ 3 + 9 * X ^ 4)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  have hrec : (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simpa using a_rec_ge m
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5) =
      X * (36 - 80 * X + 85 * X ^ 2 - 44 * X ^ 3 + 9 * X ^ 4)) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        + C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (36 - 80 * X + 85 * X ^ 2 - 44 * X ^ 3 + 9 * X ^ 4) : PowerSeries ℚ) =
        C (36 : ℚ) * X ^ 1
        - C (80 : ℚ) * X ^ 2
        + C (85 : ℚ) * X ^ 3
        - C (44 : ℚ) * X ^ 4
        + C (9 : ℚ) * X ^ 5 := by
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
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (1 / 4 : ℚ) * (n : ℚ) ^ 4 + (5 / 2 : ℚ) * (n : ℚ) ^ 3 + (37 / 4 : ℚ) * (n : ℚ) ^ 2 + 15 * n + 9 := by
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
    exact h
  exact ⟨hcf, hgf, hrec⟩


lemma col2 : ∀ j j' : Fin 2, (j' : ℕ) = j + 1 → j = 0 ∧ j' = 1 := by decide

lemma blockT : ∀ p q r s : Fin 3,
    ((((r : ℕ) : ℤ) - ((p : ℕ) : ℤ) ≤ ((s : ℕ) : ℤ) - ((q : ℕ) : ℤ)) ∧ min q p ≤ min s r) ↔
      okBlock p r q s := by decide

lemma good_iff (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 3) :
    OMA.S_oeis_a250813.Good x ↔ isValid m (Function.swap x) := by
  unfold OMA.S_oeis_a250813.Good OMA.S_oeis_a250813.BlockOK
  constructor
  · intro h i k
    fin_cases i
    exact (blockT _ _ _ _).mp (h k.castSucc k.succ (by simp) 0 1 rfl)
  · intro h i i' hi c c' hc
    obtain ⟨rfl, rfl⟩ := col2 c c' hc
    have k : ∃ k : Fin m, k.castSucc = i ∧ k.succ = i' :=
      ⟨⟨i.val, by have := i'.isLt; omega⟩, Fin.ext rfl, Fin.ext (by simp [hi])⟩
    obtain ⟨k, rfl, rfl⟩ := k
    exact (blockT _ _ _ _).mpr (h 0 k)

lemma a_eq (m : ℕ) : OMA.S_oeis_a250813.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250813.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  apply Finset.card_nbij' Function.swap Function.swap
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (good_iff (m + 1) x).mp hx
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hy ⊢
    exact (good_iff (m + 1) (Function.swap y)).mpr hy
  · intro x _; rfl
  · intro y _; rfl

theorem main_proof : type_of% @OMA.S_oeis_a250813.main := by
  obtain ⟨hcf, hgf, hrec⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250813.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250813.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega),
      hA (n - 4) (by omega), hA (n - 5) (by omega)]
    exact hrec n hn
  · rw [hser, OMA.S_oeis_a250813.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n hn]; exact hcf n hn

end OMA.P250813

theorem OMA.solution : type_of% @OMA.S_oeis_a250813.main := OMA.P250813.main_proof
