import OMAStatements.S_oeis_a259290

-- Credit: @Dariusthedoggie
-- Proof: 4-state row transfer matrix annihilated by the order-2 recurrence polynomial, giving g.f. and Binet form, bridged to the Bool pair-indexed encoding.

namespace OMA.P259290

open PowerSeries
/-- Cyclic rotation equivalence on 4-tuples of binary entries. -/
def isCyclicShift (u v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Prop :=
  u = v ∨ u = (v.2.1, v.2.2.1, v.2.2.2, v.1) ∨
  u = (v.2.2.1, v.2.2.2, v.1, v.2.1) ∨ u = (v.2.2.2, v.1, v.2.1, v.2.2.1)

instance (u v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : Decidable (isCyclicShift u v) := by
  unfold isCyclicShift; infer_instance

/-- A `2 X 2` binary subblock has clockwise pattern 0001, 0101, or 0111. -/
def okBlock (a b c d : Fin 2) : Prop :=
  isCyclicShift (a, b, d, c) (0, 0, 0, 1) ∨
  isCyclicShift (a, b, d, c) (0, 1, 0, 1) ∨
  isCyclicShift (a, b, d, c) (0, 1, 1, 1)

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 2` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 1,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A259290: Number of (n+1) X (1+1) 0..1 arrays with each 2 X 2 subblock having clockwise pattern 0001 0101 or 0111. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 2 → Fin 2

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 1, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 4 :=
  ⟨2 * (r 0).val + (r 1).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; omega⟩

def dec (k : Fin 4) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 2, by omega⟩ else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 4, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 4) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 4) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask : Fin 4 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 13
  | ⟨2, _⟩ => 11
  | ⟨3, _⟩ => 6

lemma ok2_iff : ∀ i j : Fin 4, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 4 → ℕ) (i : Fin 4) : ℕ :=
  ∑ j : Fin 4, if ok2 i j then f j else 0

def v : ℕ → Fin 4 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 4, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 4, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 4) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 4, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 : Fin 4 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

def vtab1 : Fin 4 → ℕ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 2

def vtab2 : Fin 4 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 7
  | ⟨2, _⟩ => 7
  | ⟨3, _⟩ => 6

lemma v_0 : ∀ i : Fin 4, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 4, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 4, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 4) : ℤ :=
  (v (m + 2) i : ℤ) - (v (m + 1) i : ℤ) - 4 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 4, err 0 i = 0 := by
  intro i
  change (v 2 i : ℤ) - (v 1 i : ℤ) - 4 * (v 0 i : ℤ) = 0
  simp only [v_2, v_1, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 4) :
    err (m + 1) i = ∑ j : Fin 4, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 4, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_all (m : ℕ) (i : Fin 4) : err m i = 0 := by
  induction m generalizing i with
  | zero => exact err_base i
  | succ m ih =>
    rw [err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma err_ge (m : ℕ) (i : Fin 4) : err (m + 1) i = 0 := err_all (m + 1) i

lemma a_rec_ge (m : ℕ) :
    (a (m + 3) : ℤ) = a (m + 2) + 4 * a (m + 1) := by
  have h : ∑ i : Fin 4, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 4, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 4, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  simp only [h2_1, h2_2] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 10 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 4, v 1 i = 10
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 26 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 4, v 2 i = 26
  simp only [v_2]; decide +kernel

noncomputable def cf (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (1 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17

theorem main_proof_ours :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
      2 * X * (5 + 8 * X)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((2 : ℝ) ^ (1 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17) := by
  have hrec : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
      2 * X * (5 + 8 * X) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        - C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (2 * X * (5 + 8 * X) : PowerSeries ℚ) =
        C (10 : ℚ) * X ^ 1 + C (16 : ℚ) * X ^ 2 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rcases n with _ | _ | _ | n <;> (try omega) <;> simp [a_0, a_1, a_2] <;> try norm_num
    · have hq : (a n : ℚ) = a (n - 1) + 4 * a (n - 2) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      simp only [c1, c2, e1, e2, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((2 : ℝ) ^ (1 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17 := by
    have hsq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have hbase_1 : (a 1 : ℝ) = cf 1 := by
      rw [a_1]; unfold cf
      rw [eq_div_iff (by positivity)]
      have hz : (2 : ℝ) ^ (1 - ((1 : ℕ) : ℤ)) = 1 := by norm_num
      rw [hz]
      push_cast
      ring
    have hbase_2 : (a 2 : ℝ) = cf 2 := by
      rw [a_2]; unfold cf
      rw [eq_div_iff (by positivity)]
      have hz : (2 : ℝ) ^ (1 - ((2 : ℕ) : ℤ)) = ((1 : ℝ) / 2) := by norm_num
      rw [hz]
      push_cast
      have e3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hsq]
      nlinarith [hsq, e3]
    have hf_rec : ∀ m : ℕ, cf (m + 3) = cf (m + 2) + 4 * cf (m + 1) := by
      intro m
      unfold cf
      have hchar1 : (1 - Real.sqrt 17) ^ 2 = 2 * (1 - Real.sqrt 17) + 16 := by
        nlinarith [hsq]
      have hchar2 : (1 + Real.sqrt 17) ^ 2 = 2 * (1 + Real.sqrt 17) + 16 := by
        nlinarith [hsq]
      have hz_1 : (2 : ℝ) ^ (1 - ((m + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) / (2 : ℝ) ^ 1 := by
        rw [show 1 - ((m + 2 : ℕ) : ℤ) = (1 - ((m + 1 : ℕ) : ℤ)) - ((1 : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      have hz_2 : (2 : ℝ) ^ (1 - ((m + 3 : ℕ) : ℤ)) = (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) / (2 : ℝ) ^ 2 := by
        rw [show 1 - ((m + 3 : ℕ) : ℤ) = (1 - ((m + 1 : ℕ) : ℤ)) - ((2 : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      have hp1_1 : (1 - Real.sqrt 17) ^ (m + 2) = (1 - Real.sqrt 17) ^ (m + 1) * (1 - Real.sqrt 17) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp2_1 : (1 + Real.sqrt 17) ^ (m + 2) = (1 + Real.sqrt 17) ^ (m + 1) * (1 + Real.sqrt 17) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp1_2 : (1 - Real.sqrt 17) ^ (m + 3) = (1 - Real.sqrt 17) ^ (m + 1) * (1 - Real.sqrt 17) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp2_2 : (1 + Real.sqrt 17) ^ (m + 3) = (1 + Real.sqrt 17) ^ (m + 1) * (1 + Real.sqrt 17) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      simp only [hz_1, hz_2, hp1_1, hp2_1, hp1_2, hp2_2, hchar1, hchar2]
      ring
    have hR : ∀ m : ℕ,
                (a (m + 1) : ℝ) = cf (m + 1) ∧
        (a (m + 2) : ℝ) = cf (m + 2) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hbase_1, hbase_2⟩
      | succ m ih =>
        obtain ⟨h0, h1⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), ?_⟩
        rw [show m + 1 + 2 = m + 3 by omega]
        have hr : (a (m + 3) : ℝ) = a (m + 2) + 4 * a (m + 1) := by
          have h0' := hrec (m + 3) (by omega)
          simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h0, h1, ← hf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma blk : ∀ p q r s : Fin 2,
    OMA.S_oeis_a259290.validBlock (decide (p = 1)) (decide (q = 1)) (decide (s = 1))
      (decide (r = 1)) ↔ okBlock p q r s := by decide

def toB {n : ℕ} (x : Fin (n + 1) → Fin 2 → Fin 2) : Fin (n + 1) × Fin 2 → Bool :=
  fun p => decide (x p.1 p.2 = 1)

def ofB {n : ℕ} (A : Fin (n + 1) × Fin 2 → Bool) : Fin (n + 1) → Fin 2 → Fin 2 :=
  fun i j => if A (i, j) then 1 else 0

lemma toB_ofB {n : ℕ} (A : Fin (n + 1) × Fin 2 → Bool) : toB (ofB A) = A := by
  funext p
  unfold toB ofB
  cases A (p.1, p.2) <;> simp

lemma ofB_toB {n : ℕ} (x : Fin (n + 1) → Fin 2 → Fin 2) : ofB (toB x) = x := by
  funext i j
  unfold toB ofB
  have : ∀ t : Fin 2, (if decide (t = 1) = true then (1 : Fin 2) else 0) = t := by decide
  exact this (x i j)

lemma valid_iff (n : ℕ) (x : Fin (n + 1) → Fin 2 → Fin 2) :
    (∀ i : Fin n, OMA.S_oeis_a259290.validBlock (toB x (⟨i.1, by omega⟩, 0))
      (toB x (⟨i.1, by omega⟩, 1)) (toB x (⟨i.1 + 1, by omega⟩, 1))
      (toB x (⟨i.1 + 1, by omega⟩, 0))) ↔ isValid n x := by
  constructor
  · intro h i j
    fin_cases j
    exact (blk _ _ _ _).mp (h i)
  · intro h i
    exact (blk _ _ _ _).mpr (h i 0)

lemma a_eq (m : ℕ) : OMA.S_oeis_a259290.A259290 (m + 1) = a (m + 1) := by
  unfold OMA.S_oeis_a259290.A259290
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  symm
  apply Finset.card_nbij' toB ofB
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact (valid_iff (m + 1) x).mpr hx
  · intro A hA
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hA ⊢
    apply (valid_iff (m + 1) (ofB A)).mp
    rw [toB_ofB]; exact hA
  · intro x _; exact ofB_toB x
  · intro A _; exact toB_ofB A

theorem main_proof : type_of% @OMA.S_oeis_a259290.main := by
  obtain ⟨hrec, _, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (OMA.S_oeis_a259290.A259290 n : ℤ)) =
      PowerSeries.mk (fun n => (a n : ℤ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hser, mul_comm]
    have hl : PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X - 4 * X ^ 2) =
        PowerSeries.mk (fun n => (a n : ℤ))
        - C (1 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1)
        - C (4 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (2 * X * (5 + 8 * X) : PowerSeries ℤ) =
        C (10 : ℤ) * X ^ 1 + C (16 : ℤ) * X ^ 2 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rcases n with _ | _ | _ | n <;> (try omega) <;> simp only [coeff_C, a_0, a_1, a_2] <;> norm_num [a_0, a_1, a_2]
    · have hq := hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      simp only [c1, c2, e1, e2, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [a_eq m]
    exact hcf (m + 1) hn

end OMA.P259290

theorem OMA.solution : type_of% @OMA.S_oeis_a259290.main := OMA.P259290.main_proof
