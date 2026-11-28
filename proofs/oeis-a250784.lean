import OMAStatements.S_oeis_a250784

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence and closed form bridged to upstream Blk/Good encoding.

namespace OMA.P250784

open PowerSeries

/-- A `2 X 2` `0..1` subblock `(a, b / c, d)` has `a + b ≤ c + d` and `|c - a| ≤ |d - b|`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  a.val + b.val ≤ c.val + d.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- A `3 X (m + 1)` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin 3 → Fin (m + 1) → Fin 2) : Prop :=
  ∀ i : Fin 2, ∀ j : Fin m,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin 3 → Fin (m + 1) → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250784: Number of (2+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250784 PowerSeries

abbrev Col := Fin 3 → Fin 2

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

def enc (c : Col) : Fin 8 :=
  ⟨4 * (c 0).val + 2 * (c 1).val + (c 2).val, by
    have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt; omega⟩

def dec (k : Fin 8) : Col := fun r =>
  have hk := k.isLt
  if r.val = 0 then ⟨k.val / 4, by omega⟩
  else if r.val = 1 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 8, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ c : Col, dec (enc c) = c := by
  intro c; ext r
  have h0 := (c 0).isLt; have h1 := (c 1).isLt; have h2 := (c 2).isLt
  fin_cases r
  · change (dec (enc c) 0).val = (c 0).val; simp [dec, enc]; try omega
  · change (dec (enc c) 1).val = (c 1).val; simp [dec, enc]; try omega
  · change (dec (enc c) 2).val = (c 2).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 8) : Prop := okCol (dec i) (dec j)

instance (i j : Fin 8) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 8) : ℕ := match i.val with
  | 0 => 139
  | 1 => 70
  | 2 => 32
  | 3 => 56
  | 4 => 8
  | 5 => 4
  | 6 => 2
  | 7 => 139
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 8, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 8 → ℕ) (i : Fin 8) : ℕ :=
  ∑ j : Fin 8, if ok2 i j then f j else 0

def v : ℕ → Fin 8 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Col) → ℕ) :
    ∑ x, f x = ∑ c : Col, ∑ y : Fin (m + 1) → Col, f (Fin.cons c y) := by
  rw [← (Fin.consEquiv (fun _ => Col)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Col) → ℕ) :
    ∑ y, g y = ∑ i : Fin 8, ∑ y : Fin (m + 1) → Col, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Col, ∑ i : Fin 8, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 8) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 8, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [← (Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 2)) => Fin 2)).symm.sum_comp]
  have htr : ∀ y : Fin (n + 2) → Col,
      isValid (n + 1) ((Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 2)) => Fin 2)).symm y) ↔
      isValidT (n + 1) y := fun y => isValid_transpose (n + 1) y
  simp only [htr]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 8) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | _ => 0
def vtab1 (i : Fin 8) : ℕ := match i.val with
  | 0 => 4
  | 1 => 3
  | 2 => 1
  | 3 => 3
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 4
  | _ => 0
def vtab2 (i : Fin 8) : ℕ := match i.val with
  | 0 => 14
  | 1 => 5
  | 2 => 1
  | 3 => 5
  | 4 => 3
  | 5 => 1
  | 6 => 3
  | 7 => 14
  | _ => 0
def vtab3 (i : Fin 8) : ℕ := match i.val with
  | 0 => 38
  | 1 => 9
  | 2 => 1
  | 3 => 9
  | 4 => 5
  | 5 => 1
  | 6 => 5
  | 7 => 38
  | _ => 0
def vtab4 (i : Fin 8) : ℕ := match i.val with
  | 0 => 94
  | 1 => 15
  | 2 => 1
  | 3 => 15
  | 4 => 9
  | 5 => 1
  | 6 => 9
  | 7 => 94
  | _ => 0

lemma v_0 : ∀ i : Fin 8, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 8, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 8, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 8, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 8, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 8) : ℤ :=
  (v (m + 4) i : ℤ) - 4 * (v (m + 3) i : ℤ) + 4 * (v (m + 2) i : ℤ) + (v (m + 1) i : ℤ) - 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 8, err 0 i = 0 := by
  intro i
  change (v 4 i : ℤ) - 4 * (v 3 i : ℤ) + 4 * (v 2 i : ℤ) + (v 1 i : ℤ) - 2 * (v 0 i : ℤ) = 0
  simp only [v_4, v_3, v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 8) :
    err (m + 1) i = ∑ j : Fin 8, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 8, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step, Nat.cast_sum]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> rfl
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 8) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 5) : ℤ) = 4 * a (m + 4) - 4 * a (m + 3) - a (m + 2) + 2 * a (m + 1) := by
  have h : ∑ i : Fin 8, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_all (m + 1) i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 8, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 8, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    have h0 := hsum 0; rwa [add_zero] at h0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 18 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 8, v 1 i = 18
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 46 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 8, v 2 i = 46
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 106 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 8, v 3 i = 106
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 238 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 8, v 4 i = 238
  simp only [v_4]; decide +kernel

noncomputable def cf (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 - (n : ℤ)) * ((2 : ℝ) ^ n * (1 + 11 * (2 : ℝ) ^ n) + 2 * (1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) - 2 * (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))

theorem main_proof_ours :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 4 * a (n - 2) - a (n - 3) + 2 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - X - X ^ 2)) =
      2 * X * (9 - 13 * X - 3 * X ^ 2 + 8 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (2 : ℝ) ^ (1 - (n : ℤ)) * ((2 : ℝ) ^ n * (1 + 11 * (2 : ℝ) ^ n) + 2 * (1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) - 2 * (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) := by
  have hrec : (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 4 * a (n - 2) - a (n - 3) + 2 * a (n - 4)) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simpa using a_rec_ge m
  have hgf : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - X - X ^ 2)) =
      2 * X * (9 - 13 * X - 3 * X ^ 2 + 8 * X ^ 3)) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - X - X ^ 2)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (2 * X * (9 - 13 * X - 3 * X ^ 2 + 8 * X ^ 3) : PowerSeries ℚ) =
        C (18 : ℚ) * X ^ 1
        - C (26 : ℚ) * X ^ 2
        - C (6 : ℚ) * X ^ 3
        + C (16 : ℚ) * X ^ 4 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4] <;> try norm_num
    · have hq : (a n : ℚ) = 4 * a (n - 1) - 4 * a (n - 2) - a (n - 3) + 2 * a (n - 4) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, e1, e2, e3, e4, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (2 : ℝ) ^ (1 - (n : ℤ)) * ((2 : ℝ) ^ n * (1 + 11 * (2 : ℝ) ^ n) + 2 * (1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) - 2 * (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5)) := by
    have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hb_1 : (a 1 : ℝ) = cf 1 := by
      rw [a_1]; unfold cf
      norm_num [zpow_neg, zpow_ofNat]
      linear_combination ((4 : ℝ)) * hsq
    have hb_2 : (a 2 : ℝ) = cf 2 := by
      rw [a_2]; unfold cf
      norm_num [zpow_neg, zpow_ofNat]
      linear_combination ((8 : ℝ)) * hsq
    have hb_3 : (a 3 : ℝ) = cf 3 := by
      rw [a_3]; unfold cf
      norm_num [zpow_neg, zpow_ofNat]
      linear_combination ((14 : ℝ) + (1 : ℝ) * Real.sqrt 5 ^ 2) * hsq
    have hb_4 : (a 4 : ℝ) = cf 4 := by
      rw [a_4]; unfold cf
      norm_num [zpow_neg, zpow_ofNat]
      linear_combination ((23 : ℝ) + (3 : ℝ) * Real.sqrt 5 ^ 2) * hsq
    have cf_rec : ∀ m : ℕ, cf (m + 5) = 4 * cf (m + 4) - 4 * cf (m + 3) - cf (m + 2) + 2 * cf (m + 1) := by
      intro m
      unfold cf
      have hz1 : (2 : ℝ) ^ (1 - ((m + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) * (1 / 2 : ℝ) := by
        rw [show (1 : ℤ) - ((m + 2 : ℕ) : ℤ) = (1 - ((m + 1 : ℕ) : ℤ)) + (-1 : ℤ) by push_cast; omega, zpow_add₀ (by norm_num)]
        norm_num
      have hz2 : (2 : ℝ) ^ (1 - ((m + 3 : ℕ) : ℤ)) = (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) * (1 / 4 : ℝ) := by
        rw [show (1 : ℤ) - ((m + 3 : ℕ) : ℤ) = (1 - ((m + 1 : ℕ) : ℤ)) + (-2 : ℤ) by push_cast; omega, zpow_add₀ (by norm_num)]
        norm_num
      have hz3 : (2 : ℝ) ^ (1 - ((m + 4 : ℕ) : ℤ)) = (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) * (1 / 8 : ℝ) := by
        rw [show (1 : ℤ) - ((m + 4 : ℕ) : ℤ) = (1 - ((m + 1 : ℕ) : ℤ)) + (-3 : ℤ) by push_cast; omega, zpow_add₀ (by norm_num)]
        norm_num
      have hz4 : (2 : ℝ) ^ (1 - ((m + 5 : ℕ) : ℤ)) = (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) * (1 / 16 : ℝ) := by
        rw [show (1 : ℤ) - ((m + 5 : ℕ) : ℤ) = (1 - ((m + 1 : ℕ) : ℤ)) + (-4 : ℤ) by push_cast; omega, zpow_add₀ (by norm_num)]
        norm_num
      have h2_1 : (2 : ℝ) ^ (m + 2) = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ 1 := by rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have h2_2 : (2 : ℝ) ^ (m + 3) = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ 2 := by rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have h2_3 : (2 : ℝ) ^ (m + 4) = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ 3 := by rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have h2_4 : (2 : ℝ) ^ (m + 5) = (2 : ℝ) ^ (m + 1) * (2 : ℝ) ^ 4 := by rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      have hm_1 : (1 - Real.sqrt 5) ^ (m + 2) = (1 - Real.sqrt 5) ^ (m + 1) * (1 - Real.sqrt 5) ^ 1 := by rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hm_2 : (1 - Real.sqrt 5) ^ (m + 3) = (1 - Real.sqrt 5) ^ (m + 1) * (1 - Real.sqrt 5) ^ 2 := by rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hm_3 : (1 - Real.sqrt 5) ^ (m + 4) = (1 - Real.sqrt 5) ^ (m + 1) * (1 - Real.sqrt 5) ^ 3 := by rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hm_4 : (1 - Real.sqrt 5) ^ (m + 5) = (1 - Real.sqrt 5) ^ (m + 1) * (1 - Real.sqrt 5) ^ 4 := by rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      have hp_1 : (1 + Real.sqrt 5) ^ (m + 2) = (1 + Real.sqrt 5) ^ (m + 1) * (1 + Real.sqrt 5) ^ 1 := by rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_2 : (1 + Real.sqrt 5) ^ (m + 3) = (1 + Real.sqrt 5) ^ (m + 1) * (1 + Real.sqrt 5) ^ 2 := by rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_3 : (1 + Real.sqrt 5) ^ (m + 4) = (1 + Real.sqrt 5) ^ (m + 1) * (1 + Real.sqrt 5) ^ 3 := by rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_4 : (1 + Real.sqrt 5) ^ (m + 5) = (1 + Real.sqrt 5) ^ (m + 1) * (1 + Real.sqrt 5) ^ 4 := by rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      simp only [hz1, hz2, hz3, hz4, h2_1, h2_2, h2_3, h2_4, hm_1, hm_2, hm_3, hm_4, hp_1, hp_2, hp_3, hp_4]
      generalize (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) = Z
      generalize (2 : ℝ) ^ (m + 1) = X2
      generalize (1 - Real.sqrt 5) ^ (m + 1) = Xm
      generalize (1 + Real.sqrt 5) ^ (m + 1) = Xp
      linear_combination ((-3 / 4 : ℝ) * Z * Xm + (-5 / 8 : ℝ) * Real.sqrt 5 * Z * Xm + (1 / 4 : ℝ) * Real.sqrt 5 ^ 2 * Z * Xm + (1 / 8 : ℝ) * Real.sqrt 5 ^ 3 * Z * Xm + (-3 / 4 : ℝ) * Z * Xp + (5 / 8 : ℝ) * Real.sqrt 5 * Z * Xp + (1 / 4 : ℝ) * Real.sqrt 5 ^ 2 * Z * Xp + (-1 / 8 : ℝ) * Real.sqrt 5 ^ 3 * Z * Xp) * hsq
    have hR : ∀ m : ℕ,
        (a (m + 1) : ℝ) = cf (m + 1) ∧
        (a (m + 2) : ℝ) = cf (m + 2) ∧
        (a (m + 3) : ℝ) = cf (m + 3) ∧
        (a (m + 4) : ℝ) = cf (m + 4) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_1, hb_2, hb_3, hb_4⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), (by simpa only [show m + 1 + 3 = m + 4 by omega] using h3), ?_⟩
        rw [show m + 1 + 4 = m + 5 by omega]
        have hr : (a (m + 5) : ℝ) = 4 * a (m + 4) - 4 * a (m + 3) - a (m + 2) + 2 * a (m + 1) := by
          have h0' := hrec (m + 5) (by omega)
          simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 2, OMA.S_oeis_a250784.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250784.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250784.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250784.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold OMA.S_oeis_a250784.Good isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250784.main := by
  obtain ⟨hrec, _, _⟩ := main_proof_ours
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250784.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a_eq 0]; exact a_1
  · rw [a_eq 1]; exact a_2
  · rw [a_eq 2]; exact a_3
  · rw [a_eq 3]; exact a_4
  · intro n hn
    rw [hA (n + 4) (by omega), hA (n + 3) (by omega), hA (n + 2) (by omega), hA (n + 1) (by omega), hA n (by omega)]
    have h := hrec (n + 4) (by omega)
    simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega, show n + 4 - 3 = n + 1 by omega, show n + 4 - 4 = n by omega] at h
    exact h

end OMA.P250784

theorem OMA.solution : type_of% @OMA.S_oeis_a250784.main := OMA.P250784.main_proof
