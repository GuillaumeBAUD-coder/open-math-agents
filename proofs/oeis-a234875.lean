import OMAStatements.S_oeis_a234875

-- Credit: @Dariusthedoggie
-- Proof: 25-state transfer matrix over length-2 rows of (n+1) X 2 0..4 arrays; transition operator annihilates the order-4 recurrence polynomial (shift k=1), yielding the recurrence, generating function, and closed form.

namespace OMA.P234875

open OMA.S_oeis_a234875 PowerSeries

abbrev Row := Fin 2 → Fin 5

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 1, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 25 :=
  ⟨5 * (r 0).val + (r 1).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega⟩

def dec (k : Fin 25) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 5, by omega⟩ else ⟨k.val % 5, by omega⟩

lemma enc_dec : ∀ k : Fin 25, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 25) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 25) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask (i : Fin 25) : ℕ := match i.val with
  | 0 => 0
  | 1 => 16640
  | 2 => 532992
  | 3 => 16384
  | 4 => 0
  | 5 => 4259840
  | 6 => 0
  | 7 => 16384
  | 8 => 524290
  | 9 => 4
  | 10 => 10616832
  | 11 => 4194304
  | 12 => 0
  | 13 => 4
  | 14 => 138
  | 15 => 4194304
  | 16 => 8388640
  | 17 => 1024
  | 18 => 0
  | 19 => 260
  | 20 => 0
  | 21 => 1024
  | 22 => 34848
  | 23 => 66560
  | 24 => 0
  | _ => 0

lemma ok2_iff : ∀ i j : Fin 25, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 25 → ℕ) (i : Fin 25) : ℕ :=
  ∑ j : Fin 25, if ok2 i j then f j else 0

def v : ℕ → Fin 25 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 25, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 25, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 25) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 25, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (i : Fin 25) : ℕ := match i.val with
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
  | _ => 0

def vtab1 (i : Fin 25) : ℕ := match i.val with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 0
  | 5 => 2
  | 6 => 0
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | 10 => 3
  | 11 => 1
  | 12 => 0
  | 13 => 1
  | 14 => 3
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 0
  | 19 => 2
  | 20 => 0
  | 21 => 1
  | 22 => 3
  | 23 => 2
  | 24 => 0
  | _ => 0

def vtab2 (i : Fin 25) : ℕ := match i.val with
  | 0 => 0
  | 1 => 5
  | 2 => 4
  | 3 => 3
  | 4 => 0
  | 5 => 5
  | 6 => 0
  | 7 => 3
  | 8 => 4
  | 9 => 3
  | 10 => 4
  | 11 => 3
  | 12 => 0
  | 13 => 3
  | 14 => 4
  | 15 => 3
  | 16 => 4
  | 17 => 3
  | 18 => 0
  | 19 => 5
  | 20 => 0
  | 21 => 3
  | 22 => 4
  | 23 => 5
  | 24 => 0
  | _ => 0

def vtab3 (i : Fin 25) : ℕ := match i.val with
  | 0 => 0
  | 1 => 8
  | 2 => 11
  | 3 => 4
  | 4 => 0
  | 5 => 8
  | 6 => 0
  | 7 => 4
  | 8 => 10
  | 9 => 4
  | 10 => 11
  | 11 => 4
  | 12 => 0
  | 13 => 4
  | 14 => 11
  | 15 => 4
  | 16 => 10
  | 17 => 4
  | 18 => 0
  | 19 => 8
  | 20 => 0
  | 21 => 4
  | 22 => 11
  | 23 => 8
  | 24 => 0
  | _ => 0

def vtab4 (i : Fin 25) : ℕ := match i.val with
  | 0 => 0
  | 1 => 21
  | 2 => 16
  | 3 => 11
  | 4 => 0
  | 5 => 21
  | 6 => 0
  | 7 => 11
  | 8 => 16
  | 9 => 11
  | 10 => 16
  | 11 => 11
  | 12 => 0
  | 13 => 11
  | 14 => 16
  | 15 => 11
  | 16 => 16
  | 17 => 11
  | 18 => 0
  | 19 => 21
  | 20 => 0
  | 21 => 11
  | 22 => 16
  | 23 => 21
  | 24 => 0
  | _ => 0

def vtab5 (i : Fin 25) : ℕ := match i.val with
  | 0 => 0
  | 1 => 32
  | 2 => 43
  | 3 => 16
  | 4 => 0
  | 5 => 32
  | 6 => 0
  | 7 => 16
  | 8 => 42
  | 9 => 16
  | 10 => 43
  | 11 => 16
  | 12 => 0
  | 13 => 16
  | 14 => 43
  | 15 => 16
  | 16 => 42
  | 17 => 16
  | 18 => 0
  | 19 => 32
  | 20 => 0
  | 21 => 16
  | 22 => 43
  | 23 => 32
  | 24 => 0
  | _ => 0

lemma v_0 : ∀ i : Fin 25, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 25, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 25, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 25, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel
lemma v_4 : ∀ i : Fin 25, v 4 i = vtab4 i := by
  intro i; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert i; decide +kernel
lemma v_5 : ∀ i : Fin 25, v 5 i = vtab5 i := by
  intro i; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 25) : ℤ :=
  (v (m + 4) i : ℤ) - 5 * (v (m + 2) i : ℤ) + 4 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 25, err 1 i = 0 := by
  intro i
  change (v 5 i : ℤ) - 5 * (v 3 i : ℤ) + 4 * (v 1 i : ℤ) = 0
  simp only [v_5, v_3, v_1]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 25) :
    err (m + 1) i = ∑ j : Fin 25, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 25, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 25) : err (m + 1) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 5) : ℤ) = 5 * a (m + 3) - 4 * a (m + 1) := by
  have h : ∑ i : Fin 25, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 25, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 25, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_4 : m + 1 + 4 = m + 5 := by omega
  simp only [h2_2, h2_4] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 32 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 25, v 1 i = 32
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 68 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 25, v 2 i = 68
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 128 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 25, v 3 i = 128
  simp only [v_3]; decide +kernel
lemma a_4 : a 4 = 268 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ i : Fin 25, v 4 i = 268
  simp only [v_4]; decide +kernel

def cfE (n : ℕ) : ℚ :=
  (4 + (-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3

def cfO (n : ℕ) : ℚ :=
  ((-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3

theorem main_proof :
    (∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3)) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (4 + (-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = ((-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3) := by
  have hrec : ∀ n : ℕ, 5 ≤ n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (4 * X * (8 + 17 * X - 8 * X ^ 2 - 18 * X ^ 3) : PowerSeries ℚ) =
        C (32 : ℚ) * X ^ 1 + C (68 : ℚ) * X ^ 2 - C (32 : ℚ) * X ^ 3 - C (72 : ℚ) * X ^ 4 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4] <;> try norm_num
    · have hq : (a n : ℚ) = 5 * a (n - 2) - 4 * a (n - 4) := by
        exact_mod_cast hrec n (by omega)
      have c2 : 2 ≤ n := by omega
      have c4 : 4 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      simp only [c2, c4, e1, e2, e3, e4, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf_e : ∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (4 + (-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3 := by
    have hE : ∀ m : ℕ, (a (2 * m + 2) : ℚ) = cfE (2 * m + 2) ∧ (a (2 * m + 4) : ℚ) = cfE (2 * m + 4) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add, cfE, a_2, a_4]
        norm_num
      | succ m ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨by simpa only [show 2 * (m + 1) + 2 = 2 * m + 4 by omega] using h2, ?_⟩
        rw [show 2 * (m + 1) + 4 = 2 * m + 6 by omega]
        have hr : (a (2 * m + 6) : ℚ) = 5 * a (2 * m + 4) - 4 * a (2 * m + 2) := by
          have h0' := hrec (2 * m + 6) (by omega)
          simp only [show 2 * m + 6 - 2 = 2 * m + 4 by omega, show 2 * m + 6 - 4 = 2 * m + 2 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h1, h2]
        unfold cfE
        have hp1 : (-2 : ℚ) ^ (2 * m + 6) = (-2 : ℚ) ^ (2 * m + 2) * (-2 : ℚ) ^ 4 := by
          rw [show 2 * m + 6 = (2 * m + 2) + 4 by omega, pow_add]
        have hp2 : (-2 : ℚ) ^ (2 * m + 4) = (-2 : ℚ) ^ (2 * m + 2) * (-2 : ℚ) ^ 2 := by
          rw [show 2 * m + 4 = (2 * m + 2) + 2 by omega, pow_add]
        have hp3 : (2 : ℚ) ^ (2 * m + 6) = (2 : ℚ) ^ (2 * m + 2) * (2 : ℚ) ^ 4 := by
          rw [show 2 * m + 6 = (2 * m + 2) + 4 by omega, pow_add]
        have hp4 : (2 : ℚ) ^ (2 * m + 4) = (2 : ℚ) ^ (2 * m + 2) * (2 : ℚ) ^ 2 := by
          rw [show 2 * m + 4 = (2 * m + 2) + 2 by omega, pow_add]
        rw [hp1, hp2, hp3, hp4]; ring
    intro n hn heven
    rcases heven with ⟨k, rfl⟩
    have h := (hE (k - 1)).1
    rw [show 2 * (k - 1) + 2 = k + k by omega] at h
    exact h
  have hcf_o : ∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = ((-2 : ℚ) ^ n + 49 * (2 : ℚ) ^ n) / 3 := by
    have hO : ∀ m : ℕ, (a (2 * m + 1) : ℚ) = cfO (2 * m + 1) ∧ (a (2 * m + 3) : ℚ) = cfO (2 * m + 3) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add, cfO, a_1, a_3]
        norm_num
      | succ m ih =>
        obtain ⟨h1, h2⟩ := ih
        refine ⟨by simpa only [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] using h2, ?_⟩
        rw [show 2 * (m + 1) + 3 = 2 * m + 5 by omega]
        have hr : (a (2 * m + 5) : ℚ) = 5 * a (2 * m + 3) - 4 * a (2 * m + 1) := by
          have h0' := hrec (2 * m + 5) (by omega)
          simp only [show 2 * m + 5 - 2 = 2 * m + 3 by omega, show 2 * m + 5 - 4 = 2 * m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h1, h2]
        unfold cfO
        have hp1 : (-2 : ℚ) ^ (2 * m + 5) = (-2 : ℚ) ^ (2 * m + 1) * (-2 : ℚ) ^ 4 := by
          rw [show 2 * m + 5 = (2 * m + 1) + 4 by omega, pow_add]
        have hp2 : (-2 : ℚ) ^ (2 * m + 3) = (-2 : ℚ) ^ (2 * m + 1) * (-2 : ℚ) ^ 2 := by
          rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega, pow_add]
        have hp3 : (2 : ℚ) ^ (2 * m + 5) = (2 : ℚ) ^ (2 * m + 1) * (2 : ℚ) ^ 4 := by
          rw [show 2 * m + 5 = (2 * m + 1) + 4 by omega, pow_add]
        have hp4 : (2 : ℚ) ^ (2 * m + 3) = (2 : ℚ) ^ (2 * m + 1) * (2 : ℚ) ^ 2 := by
          rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega, pow_add]
        rw [hp1, hp2, hp3, hp4]; ring
    intro n _ hodd
    rcases hodd with ⟨m, rfl⟩
    exact (hO m).1
  exact ⟨hrec, hgf, hcf_e, hcf_o⟩

end OMA.P234875

theorem OMA.solution : type_of% @OMA.S_oeis_a234875.main := OMA.P234875.main_proof
