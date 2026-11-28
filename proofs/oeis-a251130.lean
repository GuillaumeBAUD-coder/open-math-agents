import OMAStatements.S_oeis_a251130

-- Credit: @Dariusthedoggie
-- Proof: 9-state transfer matrix over length-2 rows of (n+1) X 2 0..2 arrays; transition operator annihilates the order-6 recurrence polynomial (shift k=2), yielding the recurrence, generating function, and closed form.

namespace OMA.P251130

open OMA.S_oeis_a251130 PowerSeries

abbrev Row := Fin 2 → Fin 3

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 1, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 9 :=
  ⟨3 * (r 0).val + (r 1).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega⟩

def dec (k : Fin 9) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 3, by omega⟩ else ⟨k.val % 3, by omega⟩

lemma enc_dec : ∀ k : Fin 9, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 9) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 9) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask : Fin 9 → ℕ
  | ⟨0, _⟩ => 473
  | ⟨1, _⟩ => 475
  | ⟨2, _⟩ => 511
  | ⟨3, _⟩ => 200
  | ⟨4, _⟩ => 201
  | ⟨5, _⟩ => 219
  | ⟨6, _⟩ => 64
  | ⟨7, _⟩ => 64
  | ⟨8, _⟩ => 73

lemma ok2_iff : ∀ i j : Fin 9, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 9 → ℕ) (i : Fin 9) : ℕ :=
  ∑ j : Fin 9, if ok2 i j then f j else 0

def v : ℕ → Fin 9 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 9, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 9, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 9) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 9, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 : Fin 9 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 1

def vtab1 : Fin 9 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 7
  | ⟨2, _⟩ => 9
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 4
  | ⟨5, _⟩ => 6
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 3

def vtab2 : Fin 9 → ℕ
  | ⟨0, _⟩ => 18
  | ⟨1, _⟩ => 25
  | ⟨2, _⟩ => 40
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 11
  | ⟨5, _⟩ => 22
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 10

def vtab3 : Fin 9 → ℕ
  | ⟨0, _⟩ => 46
  | ⟨1, _⟩ => 71
  | ⟨2, _⟩ => 133
  | ⟨3, _⟩ => 7
  | ⟨4, _⟩ => 25
  | ⟨5, _⟩ => 61
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 24

def vtab4 : Fin 9 → ℕ
  | ⟨0, _⟩ => 104
  | ⟨1, _⟩ => 175
  | ⟨2, _⟩ => 369
  | ⟨3, _⟩ => 9
  | ⟨4, _⟩ => 55
  | ⟨5, _⟩ => 151
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 54

def vtab5 : Fin 9 → ℕ
  | ⟨0, _⟩ => 224
  | ⟨1, _⟩ => 399
  | ⟨2, _⟩ => 919
  | ⟨3, _⟩ => 11
  | ⟨4, _⟩ => 115
  | ⟨5, _⟩ => 345
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 114

def vtab6 : Fin 9 → ℕ
  | ⟨0, _⟩ => 466
  | ⟨1, _⟩ => 865
  | ⟨2, _⟩ => 2129
  | ⟨3, _⟩ => 13
  | ⟨4, _⟩ => 237
  | ⟨5, _⟩ => 751
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 236

def vtab7 : Fin 9 → ℕ
  | ⟨0, _⟩ => 954
  | ⟨1, _⟩ => 1819
  | ⟨2, _⟩ => 4699
  | ⟨3, _⟩ => 15
  | ⟨4, _⟩ => 481
  | ⟨5, _⟩ => 1583
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 480

def vtab8 : Fin 9 → ℕ
  | ⟨0, _⟩ => 1932
  | ⟨1, _⟩ => 3751
  | ⟨2, _⟩ => 10033
  | ⟨3, _⟩ => 17
  | ⟨4, _⟩ => 971
  | ⟨5, _⟩ => 3271
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1
  | ⟨8, _⟩ => 970

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
lemma v_6 : ∀ i : Fin 9, v 6 i = vtab6 i := by
  intro i; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert i; decide +kernel
lemma v_7 : ∀ i : Fin 9, v 7 i = vtab7 i := by
  intro i; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert i; decide +kernel
lemma v_8 : ∀ i : Fin 9, v 8 i = vtab8 i := by
  intro i; rw [show (8 : ℕ) = 7 + 1 from rfl, v, step]; simp only [v_7, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 9) : ℤ :=
  (v (m + 6) i : ℤ) - 5 * (v (m + 5) i : ℤ) + 8 * (v (m + 4) i : ℤ) - 2 * (v (m + 3) i : ℤ) - 7 * (v (m + 2) i : ℤ) + 7 * (v (m + 1) i : ℤ) - 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 9, err 2 i = 0 := by
  intro i
  change (v 8 i : ℤ) - 5 * (v 7 i : ℤ) + 8 * (v 6 i : ℤ) - 2 * (v 5 i : ℤ) - 7 * (v 4 i : ℤ) + 7 * (v 3 i : ℤ) - 2 * (v 2 i : ℤ) = 0
  simp only [v_8, v_7, v_6, v_5, v_4, v_3, v_2]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 9) :
    err (m + 1) i = ∑ j : Fin 9, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 9, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 9) : err (m + 2) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 8) : ℤ) = 5 * a (m + 7) - 8 * a (m + 6) + 2 * a (m + 5) + 7 * a (m + 4) - 7 * a (m + 3) + 2 * a (m + 2) := by
  have h : ∑ i : Fin 9, err (m + 2) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 9, (v (m + 2 + r) i : ℤ)) = (a (m + 2 + r) : ℤ) := by
    intro r
    have h1 : m + 2 + r = (m + 1 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 9, (v (m + 2) i : ℤ)) = (a (m + 2) : ℤ) := by
    simpa using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 2 + 1 = m + 3 := by omega
  have h2_2 : m + 2 + 2 = m + 4 := by omega
  have h2_3 : m + 2 + 3 = m + 5 := by omega
  have h2_4 : m + 2 + 4 = m + 6 := by omega
  have h2_5 : m + 2 + 5 = m + 7 := by omega
  have h2_6 : m + 2 + 6 = m + 8 := by omega
  simp only [h2_1, h2_2, h2_3, h2_4, h2_5, h2_6] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 40 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 1 i = 40
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 133 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 2 i = 133
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 369 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 3 i = 369
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 919 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 4 i = 919
  simp only [v_4]; decide +kernel
lemma a_5 : a 5 = 2129 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 5 i = 2129
  simp only [v_5]; decide +kernel
lemma a_6 : a 6 = 4699 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 6 i = 4699
  simp only [v_6]; decide +kernel
lemma a_7 : a 7 = 10033 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ i : Fin 9, v 7 i = 10033
  simp only [v_7]; decide +kernel

def cf (n : ℕ) : ℚ :=
  (-957 + (-1 : ℚ) ^ n + 529 * (2 : ℚ) ^ (1 + n) - 540 * n - 126 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) / 12

theorem main_proof :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 2 * a (n - 3) + 7 * a (n - 4) - 7 * a (n - 5) + 2 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) * (1 - 2 * X)) =
      X * (40 - 67 * X + 24 * X ^ 2 + 58 * X ^ 3 - 60 * X ^ 4 + 17 * X ^ 5)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-957 + (-1 : ℚ) ^ n + 529 * (2 : ℚ) ^ (1 + n) - 540 * n - 126 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) / 12) := by
  have hrec : ∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 2 * a (n - 3) + 7 * a (n - 4) - 7 * a (n - 5) + 2 * a (n - 6) := by
    intro n hn
    rcases Nat.lt_or_ge n 8 with hlt | hge
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) * (1 - 2 * X)) =
      X * (40 - 67 * X + 24 * X ^ 2 + 58 * X ^ 3 - 60 * X ^ 4 + 17 * X ^ 5) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) * (1 - 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (8 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        + C (7 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5)
        - C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 6) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (40 - 67 * X + 24 * X ^ 2 + 58 * X ^ 3 - 60 * X ^ 4 + 17 * X ^ 5) : PowerSeries ℚ) =
        C (40 : ℚ) * X ^ 1 - C (67 : ℚ) * X ^ 2 + C (24 : ℚ) * X ^ 3 + C (58 : ℚ) * X ^ 4 - C (60 : ℚ) * X ^ 5 + C (17 : ℚ) * X ^ 6 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> try norm_num
    · have hq : (a n : ℚ) = 5 * a (n - 1) - 8 * a (n - 2) + 2 * a (n - 3) + 7 * a (n - 4) - 7 * a (n - 5) + 2 * a (n - 6) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have c5 : 5 ≤ n := by omega
      have c6 : 6 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      have e6 : n - 6 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, c5, c6, e1, e2, e3, e4, e5, e6, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-957 + (-1 : ℚ) ^ n + 529 * (2 : ℚ) ^ (1 + n) - 540 * n - 126 * (n : ℚ) ^ 2 - 12 * (n : ℚ) ^ 3) / 12 := by
    have hQ : ∀ m : ℕ,
                (a (m + 1) : ℚ) = cf (m + 1) ∧
        (a (m + 2) : ℚ) = cf (m + 2) ∧
        (a (m + 3) : ℚ) = cf (m + 3) ∧
        (a (m + 4) : ℚ) = cf (m + 4) ∧
        (a (m + 5) : ℚ) = cf (m + 5) ∧
        (a (m + 6) : ℚ) = cf (m + 6) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add, cf, a_1, a_2, a_3, a_4, a_5, a_6]
        norm_num
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), (by simpa only [show m + 1 + 3 = m + 4 by omega] using h3), (by simpa only [show m + 1 + 4 = m + 5 by omega] using h4), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h5), ?_⟩
        rw [show m + 1 + 6 = m + 7 by omega]
        have hr : (a (m + 7) : ℚ) = 5 * a (m + 6) - 8 * a (m + 5) + 2 * a (m + 4) + 7 * a (m + 3) - 7 * a (m + 2) + 2 * a (m + 1) := by
          have h0' := hrec (m + 7) (by omega)
          simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h0, h1, h2, h3, h4, h5]
        unfold cf
        have hp0_1 : (-1 : ℚ) ^ (m + 2) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 1 := by rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
        have hp0_2 : (-1 : ℚ) ^ (m + 3) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 2 := by rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
        have hp0_3 : (-1 : ℚ) ^ (m + 4) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 3 := by rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
        have hp0_4 : (-1 : ℚ) ^ (m + 5) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 4 := by rw [show m + 5 = (m + 1) + 4 by omega, pow_add]
        have hp0_5 : (-1 : ℚ) ^ (m + 6) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 5 := by rw [show m + 6 = (m + 1) + 5 by omega, pow_add]
        have hp0_6 : (-1 : ℚ) ^ (m + 7) = (-1 : ℚ) ^ (m + 1) * (-1 : ℚ) ^ 6 := by rw [show m + 7 = (m + 1) + 6 by omega, pow_add]
        have hp1_1 : (2 : ℚ) ^ (1 + (m + 2)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 1 := by rw [show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_add]
        have hp1_2 : (2 : ℚ) ^ (1 + (m + 3)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 2 := by rw [show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega, pow_add]
        have hp1_3 : (2 : ℚ) ^ (1 + (m + 4)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 3 := by rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega, pow_add]
        have hp1_4 : (2 : ℚ) ^ (1 + (m + 5)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 4 := by rw [show 1 + (m + 5) = (1 + (m + 1)) + 4 by omega, pow_add]
        have hp1_5 : (2 : ℚ) ^ (1 + (m + 6)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 5 := by rw [show 1 + (m + 6) = (1 + (m + 1)) + 5 by omega, pow_add]
        have hp1_6 : (2 : ℚ) ^ (1 + (m + 7)) = (2 : ℚ) ^ (1 + (m + 1)) * (2 : ℚ) ^ 6 := by rw [show 1 + (m + 7) = (1 + (m + 1)) + 6 by omega, pow_add]
        simp only [hp0_1, hp0_2, hp0_3, hp0_4, hp0_5, hp0_6, hp1_1, hp1_2, hp1_3, hp1_4, hp1_5, hp1_6]
        push_cast
        ring
    intro n hn
    have h := (hQ (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩

end OMA.P251130

theorem OMA.solution : type_of% @OMA.S_oeis_a251130.main := OMA.P251130.main_proof
