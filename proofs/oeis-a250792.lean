import OMAStatements.S_oeis_a250792

-- Credit: @Dariusthedoggie
-- Proof: row transfer matrix annihilated by the order-5 recurrence polynomial, giving recurrence, g.f. and closed form, bridged to the Nat.card encoding.

namespace OMA.P250792

open PowerSeries
/-- A `2 X 2` binary subblock `(a, b / c, d)` has `min a b ≤ min c d` and `|c - a| ≤ |d - b|`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  min a.val b.val ≤ min c.val d.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 4` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 3,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250792: Number of (n+1) X (3+1) 0..1 arrays with nondecreasing min(x(i,j),x(i,j-1)) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 4 → Fin 2

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 3, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 16 :=
  ⟨8 * (r 0).val + 4 * (r 1).val + 2 * (r 2).val + (r 3).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt; omega⟩

def dec (k : Fin 16) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 8, by omega⟩
  else if c.val = 1 then ⟨(k.val / 4) % 2, by omega⟩
  else if c.val = 2 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 16, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; have h3 := (r 3).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega
  · change (dec (enc r) 3).val = (r 3).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 16) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 16) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 16) : ℕ := match i.val with
  | 0 => 32907
  | 1 => 16455
  | 2 => 8238
  | 3 => 8
  | 4 => 2232
  | 5 => 1140
  | 6 => 192
  | 7 => 128
  | 8 => 35712
  | 9 => 18240
  | 10 => 11808
  | 11 => 2048
  | 12 => 45056
  | 13 => 28672
  | 14 => 49152
  | 15 => 32768
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 16, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 16 → ℕ) (i : Fin 16) : ℕ :=
  ∑ j : Fin 16, if ok2 i j then f j else 0

def v : ℕ → Fin 16 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 16, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 16, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 16) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 16, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 16) : ℕ := match i.val with
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
  | _ => 0

def vtab1 (i : Fin 16) : ℕ := match i.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 1
  | 4 => 5
  | 5 => 5
  | 6 => 2
  | 7 => 1
  | 8 => 5
  | 9 => 5
  | 10 => 5
  | 11 => 1
  | 12 => 3
  | 13 => 3
  | 14 => 2
  | 15 => 1
  | _ => 0

def vtab2 (i : Fin 16) : ℕ := match i.val with
  | 0 => 13
  | 1 => 19
  | 2 => 19
  | 3 => 1
  | 4 => 13
  | 5 => 22
  | 6 => 3
  | 7 => 1
  | 8 => 13
  | 9 => 19
  | 10 => 19
  | 11 => 1
  | 12 => 7
  | 13 => 8
  | 14 => 3
  | 15 => 1
  | _ => 0

def vtab3 (i : Fin 16) : ℕ := match i.val with
  | 0 => 35
  | 1 => 57
  | 2 => 69
  | 3 => 1
  | 4 => 38
  | 5 => 76
  | 6 => 4
  | 7 => 1
  | 8 => 35
  | 9 => 57
  | 10 => 69
  | 11 => 1
  | 12 => 16
  | 13 => 18
  | 14 => 4
  | 15 => 1
  | _ => 0

def vtab4 (i : Fin 16) : ℕ := match i.val with
  | 0 => 95
  | 1 => 169
  | 2 => 221
  | 3 => 1
  | 4 => 117
  | 5 => 256
  | 6 => 5
  | 7 => 1
  | 8 => 95
  | 9 => 169
  | 10 => 221
  | 11 => 1
  | 12 => 35
  | 13 => 38
  | 14 => 5
  | 15 => 1
  | _ => 0

def vtab5 (i : Fin 16) : ℕ := match i.val with
  | 0 => 267
  | 1 => 495
  | 2 => 685
  | 3 => 1
  | 4 => 376
  | 5 => 820
  | 6 => 6
  | 7 => 1
  | 8 => 267
  | 9 => 495
  | 10 => 685
  | 11 => 1
  | 12 => 74
  | 13 => 78
  | 14 => 6
  | 15 => 1
  | _ => 0

def vtab6 (i : Fin 16) : ℕ := match i.val with
  | 0 => 765
  | 1 => 1459
  | 2 => 2079
  | 3 => 1
  | 4 => 1199
  | 5 => 2572
  | 6 => 7
  | 7 => 1
  | 8 => 765
  | 9 => 1459
  | 10 => 2079
  | 11 => 1
  | 12 => 153
  | 13 => 158
  | 14 => 7
  | 15 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 16, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 16, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 16, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 16, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 16, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 16, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel
lemma v_6 : ∀ i : Fin 16, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 16) : ℤ :=
  (v (m + 5) i : ℤ) - 6 * (v (m + 4) i : ℤ) + 10 * (v (m + 3) i : ℤ) - 11 * (v (m + 1) i : ℤ) + 6 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 16, err 1 i = 0 := by
  intro i
  change (v 6 i : ℤ) - 6 * (v 5 i : ℤ) + 10 * (v 4 i : ℤ) - 11 * (v 2 i : ℤ) + 6 * (v 1 i : ℤ) = 0
  simp only [v_6, v_5, v_4, v_2, v_1]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 16) :
    err (m + 1) i = ∑ j : Fin 16, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 16, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 16) : err (m + 1) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 6) : ℤ) = 6 * a (m + 5) - 10 * a (m + 4) + 11 * a (m + 2) - 6 * a (m + 1) := by
  have h : ∑ i : Fin 16, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 16, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 16, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  have h2_5 : m + 1 + 5 = m + 6 := by omega
  simp only [h2_1, h2_3, h2_4, h2_5] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 54 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 1 i = 54
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 162 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 2 i = 162
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 482 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 3 i = 482
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 1430 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 4 i = 1430
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 4258 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 5 i = 4258
  simp only [v_5]; decide +kernel

def cf (n : ℕ) : ℚ :=
  -3 - (-1 : ℚ) ^ n / 4 + (2 : ℚ) ^ (1 + n) + 23 * (3 : ℚ) ^ (1 + n) / 4 + (n : ℚ)


theorem main_proof_ours :
    (∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 10 * a (n - 2) + 11 * a (n - 4) - 6 * a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 - 2 * X) * (1 - 3 * X)) =
      2 * X * (27 - 81 * X + 25 * X ^ 2 + 79 * X ^ 3 - 48 * X ^ 4)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = -3 - (-1 : ℚ) ^ n / 4 + (2 : ℚ) ^ (1 + n) + 23 * (3 : ℚ) ^ (1 + n) / 4 + (n : ℚ)) := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 10 * a (n - 2) + 11 * a (n - 4) - 6 * a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 - 2 * X) * (1 - 3 * X)) =
      2 * X * (27 - 81 * X + 25 * X ^ 2 + 79 * X ^ 3 - 48 * X ^ 4) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) * (1 - 2 * X) * (1 - 3 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (10 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (11 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        + C (6 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (2 * X * (27 - 81 * X + 25 * X ^ 2 + 79 * X ^ 3 - 48 * X ^ 4) : PowerSeries ℚ) =
        C (54 : ℚ) * X ^ 1 - C (162 : ℚ) * X ^ 2 + C (50 : ℚ) * X ^ 3 + C (158 : ℚ) * X ^ 4 - C (96 : ℚ) * X ^ 5 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5] <;> try norm_num
    · have hq : (a n : ℚ) = 6 * a (n - 1) - 10 * a (n - 2) + 11 * a (n - 4) - 6 * a (n - 5) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have c5 : 5 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      simp only [c1, c2, c4, c5, e1, e2, e3, e4, e5, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = -3 - (-1 : ℚ) ^ n / 4 + (2 : ℚ) ^ (1 + n) + 23 * (3 : ℚ) ^ (1 + n) / 4 + (n : ℚ) := by
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
    have cf_rec : ∀ m : ℕ, cf (m + 6) = 6 * cf (m + 5) - 10 * cf (m + 4) + 11 * cf (m + 2) - 6 * cf (m + 1) := by
      intro m
      unfold cf
      have hp_a_1 : (-1 : ℚ) ^ (m + 2) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_a_2 : (-1 : ℚ) ^ (m + 3) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_a_3 : (-1 : ℚ) ^ (m + 4) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_a_4 : (-1 : ℚ) ^ (m + 5) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 4 := by
        rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
      have hp_a_5 : (-1 : ℚ) ^ (m + 6) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 5 := by
        rw [show m + 6 = (m + 1) + 5 by omega, pow_add]
      have hp_b_1 : (2 : ℚ) ^ (1 + (m + 2)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 1 := by
        rw [show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_add]
      have hp_b_2 : (2 : ℚ) ^ (1 + (m + 3)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 2 := by
        rw [show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega, pow_add]
      have hp_b_3 : (2 : ℚ) ^ (1 + (m + 4)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 3 := by
        rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega, pow_add]
      have hp_b_4 : (2 : ℚ) ^ (1 + (m + 5)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 4 := by
        rw [show 1 + (m + 5) = (1 + (m + 1)) + 4 by omega, pow_add]
      have hp_b_5 : (2 : ℚ) ^ (1 + (m + 6)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 5 := by
        rw [show 1 + (m + 6) = (1 + (m + 1)) + 5 by omega, pow_add]
      have hp_c_1 : (3 : ℚ) ^ (1 + (m + 2)) = (3 : ℚ) ^ (1 + (m + 1)) * (3 : ℚ) ^ 1 := by
        rw [show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_add]
      have hp_c_2 : (3 : ℚ) ^ (1 + (m + 3)) = (3 : ℚ) ^ (1 + (m + 1)) * (3 : ℚ) ^ 2 := by
        rw [show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega, pow_add]
      have hp_c_3 : (3 : ℚ) ^ (1 + (m + 4)) = (3 : ℚ) ^ (1 + (m + 1)) * (3 : ℚ) ^ 3 := by
        rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega, pow_add]
      have hp_c_4 : (3 : ℚ) ^ (1 + (m + 5)) = (3 : ℚ) ^ (1 + (m + 1)) * (3 : ℚ) ^ 4 := by
        rw [show 1 + (m + 5) = (1 + (m + 1)) + 4 by omega, pow_add]
      have hp_c_5 : (3 : ℚ) ^ (1 + (m + 6)) = (3 : ℚ) ^ (1 + (m + 1)) * (3 : ℚ) ^ 5 := by
        rw [show 1 + (m + 6) = (1 + (m + 1)) + 5 by omega, pow_add]
      simp only [hp_a_1, hp_a_2, hp_a_3, hp_a_4, hp_a_5, hp_b_1, hp_b_2, hp_b_3, hp_b_4, hp_b_5, hp_c_1, hp_c_2, hp_c_3, hp_c_4, hp_c_5]
      generalize (-1 : ℚ) ^ (m + 1) = Xa
      generalize (2 : ℚ) ^ (1 + (m + 1)) = Xb
      generalize (3 : ℚ) ^ (1 + (m + 1)) = Xc
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
        have hr : (a (m + 6) : ℚ) = 6 * a (m + 5) - 10 * a (m + 4) + 11 * a (m + 2) - 6 * a (m + 1) := by
          have h0' := hrec (m + 6) (by omega)
          simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h4, h3, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 2, OMA.S_oeis_a250792.Blk p q r s ↔ okBlock p q r s := by
  simp only [OMA.S_oeis_a250792.Blk, okBlock]
  decide

lemma a_eq (m : ℕ) : OMA.S_oeis_a250792.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250792.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [blk]

theorem main_proof : type_of% @OMA.S_oeis_a250792.main := by
  obtain ⟨hrec, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250792.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250792.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 4) (by omega), hA (n - 5) (by omega)]
    exact hrec n hn
  · rw [hser, OMA.S_oeis_a250792.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · exact hgf
    · simp
  · rw [hA n (by omega)]; exact hcf n hn

end OMA.P250792

theorem OMA.solution : type_of% @OMA.S_oeis_a250792.main := OMA.P250792.main_proof
