import OMAStatements.S_oeis_a250778

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix recurrence, g.f. and closed form bridged to upstream PairOK encoding.

namespace OMA.P250778

open PowerSeries

/-- A `2 X 2` binary subblock `(a, b / c, d)` has `a + b ≤ c + d` and `|c - a| ≤ |d - b|`. -/
def okBlock (a b c d : Fin 2) : Prop :=
  a.val + b.val ≤ c.val + d.val ∧ |(c.val : ℤ) - a.val| ≤ |(d.val : ℤ) - b.val|

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 4` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 3,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 4 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A250778: Number of (n+1) X (3+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card


open OMA.S_oeis_a250778 PowerSeries

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
  | 1 => 16454
  | 2 => 8236
  | 3 => 8
  | 4 => 2224
  | 5 => 1120
  | 6 => 192
  | 7 => 128
  | 8 => 35712
  | 9 => 17984
  | 10 => 11296
  | 11 => 2048
  | 12 => 45056
  | 13 => 24576
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
  | 1 => 4
  | 2 => 4
  | 3 => 1
  | 4 => 4
  | 5 => 3
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
  | _ => 0

def vtab2 (i : Fin 16) : ℕ := match i.val with
  | 0 => 12
  | 1 => 12
  | 2 => 10
  | 3 => 1
  | 4 => 9
  | 5 => 9
  | 6 => 3
  | 7 => 1
  | 8 => 12
  | 9 => 12
  | 10 => 10
  | 11 => 1
  | 12 => 6
  | 13 => 4
  | 14 => 3
  | 15 => 1
  | _ => 0

def vtab3 (i : Fin 16) : ℕ := match i.val with
  | 0 => 27
  | 1 => 28
  | 2 => 24
  | 3 => 1
  | 4 => 20
  | 5 => 22
  | 6 => 4
  | 7 => 1
  | 8 => 27
  | 9 => 28
  | 10 => 24
  | 11 => 1
  | 12 => 11
  | 13 => 7
  | 14 => 4
  | 15 => 1
  | _ => 0

def vtab4 (i : Fin 16) : ℕ := match i.val with
  | 0 => 58
  | 1 => 60
  | 2 => 54
  | 3 => 1
  | 4 => 44
  | 5 => 50
  | 6 => 5
  | 7 => 1
  | 8 => 58
  | 9 => 60
  | 10 => 54
  | 11 => 1
  | 12 => 19
  | 13 => 11
  | 14 => 5
  | 15 => 1
  | _ => 0

def vtab5 (i : Fin 16) : ℕ := match i.val with
  | 0 => 121
  | 1 => 124
  | 2 => 116
  | 3 => 1
  | 4 => 96
  | 5 => 109
  | 6 => 6
  | 7 => 1
  | 8 => 121
  | 9 => 124
  | 10 => 116
  | 11 => 1
  | 12 => 31
  | 13 => 16
  | 14 => 6
  | 15 => 1
  | _ => 0

def vtab6 (i : Fin 16) : ℕ := match i.val with
  | 0 => 248
  | 1 => 252
  | 2 => 242
  | 3 => 1
  | 4 => 207
  | 5 => 231
  | 6 => 7
  | 7 => 1
  | 8 => 248
  | 9 => 252
  | 10 => 242
  | 11 => 1
  | 12 => 48
  | 13 => 22
  | 14 => 7
  | 15 => 1
  | _ => 0

def vtab7 (i : Fin 16) : ℕ := match i.val with
  | 0 => 503
  | 1 => 508
  | 2 => 496
  | 3 => 1
  | 4 => 440
  | 5 => 480
  | 6 => 8
  | 7 => 1
  | 8 => 503
  | 9 => 508
  | 10 => 496
  | 11 => 1
  | 12 => 71
  | 13 => 29
  | 14 => 8
  | 15 => 1
  | _ => 0

def vtab8 (i : Fin 16) : ℕ := match i.val with
  | 0 => 1014
  | 1 => 1020
  | 2 => 1006
  | 3 => 1
  | 4 => 922
  | 5 => 984
  | 6 => 9
  | 7 => 1
  | 8 => 1014
  | 9 => 1020
  | 10 => 1006
  | 11 => 1
  | 12 => 101
  | 13 => 37
  | 14 => 9
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
lemma v_7 : ∀ i : Fin 16, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 16, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 16) : ℤ :=
  (v (m + 5) i : ℤ) - 6 * (v (m + 4) i : ℤ) + 14 * (v (m + 3) i : ℤ) - 16 * (v (m + 2) i : ℤ) + 9 * (v (m + 1) i : ℤ) - 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 16, err 1 i = 0 := by
  intro i
  change (v 6 i : ℤ) - 6 * (v 5 i : ℤ) + 14 * (v 4 i : ℤ) - 16 * (v 3 i : ℤ) + 9 * (v 2 i : ℤ) - 2 * (v 1 i : ℤ) = 0
  simp only [v_6, v_5, v_4, v_3, v_2, v_1]
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

lemma a_rec_m (m : ℕ) :
    (a (m + 6) : ℤ) = 6 * a (m + 5) - 14 * a (m + 4) + 16 * a (m + 3) - 9 * a (m + 2) + 2 * a (m + 1) := by
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
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  have h2_5 : m + 1 + 5 = m + 6 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 46 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 1 i = 46
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 106 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 2 i = 106
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 230 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 3 i = 230
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 482 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 4 i = 482
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 990 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 5 i = 990
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 2010 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 6 i = 2010
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 4054 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 7 i = 4054
  simp only [v_7]; decide +kernel
lemma a_8 : a 8 = 8146 := by
  rw [show (8 : ℕ) = 7 + 1 from rfl, a_succ]
  change ∑ i : Fin 16, v 8 i = 8146
  simp only [v_8]; decide +kernel

def e (m : ℕ) : ℤ := (a (m + 4) : ℤ) - (4 * a (m + 3) - 5 * a (m + 2) + 2 * a (m + 1))

lemma e_rec (m : ℕ) : e (m + 5) = 6 * e (m + 4) - 14 * e (m + 3) + 16 * e (m + 2) - 9 * e (m + 1) + 2 * e m := by
  have g0 : (a (m + 9) : ℤ) = 6 * a (m + 8) - 14 * a (m + 7) + 16 * a (m + 6) - 9 * a (m + 5) + 2 * a (m + 4) := by
    have h := a_rec_m (m + 3)
    simp only [show m + 3 + 6 = m + 9 by omega, show m + 3 + 5 = m + 8 by omega, show m + 3 + 4 = m + 7 by omega, show m + 3 + 3 = m + 6 by omega, show m + 3 + 2 = m + 5 by omega, show m + 3 + 1 = m + 4 by omega] at h
    exact h
  have g1 : (a (m + 8) : ℤ) = 6 * a (m + 7) - 14 * a (m + 6) + 16 * a (m + 5) - 9 * a (m + 4) + 2 * a (m + 3) := by
    have h := a_rec_m (m + 2)
    simp only [show m + 2 + 6 = m + 8 by omega, show m + 2 + 5 = m + 7 by omega, show m + 2 + 4 = m + 6 by omega, show m + 2 + 3 = m + 5 by omega, show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega] at h
    exact h
  have g2 : (a (m + 7) : ℤ) = 6 * a (m + 6) - 14 * a (m + 5) + 16 * a (m + 4) - 9 * a (m + 3) + 2 * a (m + 2) := by
    have h := a_rec_m (m + 1)
    simp only [show m + 1 + 6 = m + 7 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at h
    exact h
  have g3 : (a (m + 6) : ℤ) = 6 * a (m + 5) - 14 * a (m + 4) + 16 * a (m + 3) - 9 * a (m + 2) + 2 * a (m + 1) := by
    have h := a_rec_m (m + 0)
    simp only [show m + 0 + 6 = m + 6 by omega, show m + 0 + 5 = m + 5 by omega, show m + 0 + 4 = m + 4 by omega, show m + 0 + 3 = m + 3 by omega, show m + 0 + 2 = m + 2 by omega, show m + 0 + 1 = m + 1 by omega] at h
    exact h
  simp only [e, show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 4 = m + 5 by omega, show m + 2 + 1 = m + 3 by omega, show m + 2 + 2 = m + 4 by omega, show m + 2 + 3 = m + 5 by omega, show m + 2 + 4 = m + 6 by omega, show m + 3 + 1 = m + 4 by omega, show m + 3 + 2 = m + 5 by omega, show m + 3 + 3 = m + 6 by omega, show m + 3 + 4 = m + 7 by omega, show m + 4 + 1 = m + 5 by omega, show m + 4 + 2 = m + 6 by omega, show m + 4 + 3 = m + 7 by omega, show m + 4 + 4 = m + 8 by omega, show m + 5 + 1 = m + 6 by omega, show m + 5 + 2 = m + 7 by omega, show m + 5 + 3 = m + 8 by omega, show m + 5 + 4 = m + 9 by omega]
  linear_combination (1) * g0 + (-4) * g1 + (5) * g2 + (-2) * g3

lemma e_zero : ∀ m : ℕ, e m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 5 with h | h
    · interval_cases m <;> norm_num [e, a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8]
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 5 := ⟨m - 5, by omega⟩
      rw [e_rec t]
      simp [ih (t + 4) (by omega), ih (t + 3) (by omega), ih (t + 2) (by omega), ih (t + 1) (by omega), ih t (by omega)]

lemma a_rec_ge (m : ℕ) :
    (a (m + 4) : ℤ) = 4 * a (m + 3) - 5 * a (m + 2) + 2 * a (m + 1) := by
  have h := e_zero m
  unfold e at h
  linarith

def cf (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (5 + n) - 4 * (n : ℚ) - 14


theorem main_proof_ours :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X)) =
      2 * X * (23 - 39 * X + 18 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 : ℚ) ^ (5 + n) - 4 * (n : ℚ) - 14) := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X)) =
      2 * X * (23 - 39 * X + 18 * X ^ 2) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 - 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (2 * X * (23 - 39 * X + 18 * X ^ 2) : PowerSeries ℚ) =
        C (46 : ℚ) * X ^ 1 - C (78 : ℚ) * X ^ 2 + C (36 : ℚ) * X ^ 3 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> try norm_num
    · have hq : (a n : ℚ) = 4 * a (n - 1) - 5 * a (n - 2) + 2 * a (n - 3) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      simp only [c1, c2, c3, e1, e2, e3, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 : ℚ) ^ (5 + n) - 4 * (n : ℚ) - 14 := by
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
    have cf_rec : ∀ m : ℕ, cf (m + 4) = 4 * cf (m + 3) - 5 * cf (m + 2) + 2 * cf (m + 1) := by
      intro m
      unfold cf
      have hp_t_1 : (2 : ℚ) ^ (5 + (m + 2)) = (2 : ℚ) ^ (5 + (m + 1)) * (2 : ℚ) ^ 1 := by
        rw [show 5 + (m + 2) = (5 + (m + 1)) + 1 by omega, pow_add]
      have hp_t_2 : (2 : ℚ) ^ (5 + (m + 3)) = (2 : ℚ) ^ (5 + (m + 1)) * (2 : ℚ) ^ 2 := by
        rw [show 5 + (m + 3) = (5 + (m + 1)) + 2 by omega, pow_add]
      have hp_t_3 : (2 : ℚ) ^ (5 + (m + 4)) = (2 : ℚ) ^ (5 + (m + 1)) * (2 : ℚ) ^ 3 := by
        rw [show 5 + (m + 4) = (5 + (m + 1)) + 3 by omega, pow_add]
      simp only [hp_t_1, hp_t_2, hp_t_3]
      generalize (2 : ℚ) ^ (5 + (m + 1)) = Xt
      push_cast
      ring
    have hR : ∀ m : ℕ,
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
        have hr : (a (m + 4) : ℚ) = 4 * a (m + 3) - 5 * a (m + 2) + 2 * a (m + 1) := by
          have h0' := hrec (m + 4) (by omega)
          simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk_pair (a b c d : Fin 2) :
    (((b : ℕ) : ℤ) + ((a : ℕ) : ℤ) ≤ ((d : ℕ) : ℤ) + ((c : ℕ) : ℤ) ∧
      |((c : ℕ) : ℤ) - ((a : ℕ) : ℤ)| ≤ |((d : ℕ) : ℤ) - ((b : ℕ) : ℤ)|) ↔
      okBlock a b c d := by
  unfold okBlock
  revert a b c d
  decide

lemma pairOK_iff (u v : Fin 4 → Fin 2) :
    OMA.S_oeis_a250778.PairOK u v ↔
      ∀ j : Fin 3, okBlock (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ) := by
  unfold OMA.S_oeis_a250778.PairOK
  simp only [blk_pair]

lemma a_eq (m : ℕ) : OMA.S_oeis_a250778.a (m + 1) = a (m + 1) := by
  classical
  unfold OMA.S_oeis_a250778.a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold isValid
  simp only [pairOK_iff]

theorem main_proof : type_of% @OMA.S_oeis_a250778.main := by
  obtain ⟨hrec, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a250778.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 ≤ n → OMA.S_oeis_a250778.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · rw [hA n (by omega), hA (n - 1) (by omega), hA (n - 2) (by omega), hA (n - 3) (by omega)]
    exact hrec n (by omega)
  · rw [hser, OMA.S_oeis_a250778.G, PowerSeries.eq_mul_inv_iff_mul_eq]
    · rw [hgf]; ring
    · simp
  · rw [hA n (by omega)]
    exact hcf n (by omega)

end OMA.P250778

theorem OMA.solution : type_of% @OMA.S_oeis_a250778.main := OMA.P250778.main_proof
