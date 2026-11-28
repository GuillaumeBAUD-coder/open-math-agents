import OMAStatements.S_oeis_a250461

-- Credit: @Dariusthedoggie
-- Proof: 4-state transfer matrix over length-2 rows of (n+1) X 2 0..1 arrays; the per-state count vectors satisfy an order-3 linear recurrence (from shift 0), checked by kernel decide on the initial vectors; the generating function and closed form(s) follow from the recurrence and initial terms (closed forms with square roots via linear_combination modulo sqrt(D)^2 = D).

namespace OMA.P250461

open OMA.S_oeis_a250461 PowerSeries

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

def adjMask (i : Fin 4) : ℕ := match i.val with
  | 0 => 15
  | 1 => 15
  | 2 => 3
  | 3 => 8
  | _ => 0

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

def vtab0 (i : Fin 4) : ℕ := match i.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | _ => 0

def vtab1 (i : Fin 4) : ℕ := match i.val with
  | 0 => 4
  | 1 => 4
  | 2 => 2
  | 3 => 1
  | _ => 0

def vtab2 (i : Fin 4) : ℕ := match i.val with
  | 0 => 11
  | 1 => 11
  | 2 => 8
  | 3 => 1
  | _ => 0

def vtab3 (i : Fin 4) : ℕ := match i.val with
  | 0 => 31
  | 1 => 31
  | 2 => 22
  | 3 => 1
  | _ => 0

lemma v_0 : ∀ i : Fin 4, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 4, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 4, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 4, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 4) : ℤ :=
  (v (m + 3) i : ℤ) - 3 * (v (m + 2) i : ℤ) + 2 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 4, err 0 i = 0 := by
  intro i
  change (v 3 i : ℤ) - 3 * (v 2 i : ℤ) + 2 * (v 0 i : ℤ) = 0
  simp only [v_3, v_2, v_0]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 4) :
    err (m + 1) i = ∑ j : Fin 4, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 4, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
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
    (a (m + 4) : ℤ) = 3 * a (m + 3) - 2 * a (m + 1) := by
  have h : ∑ i : Fin 4, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 4, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 4, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa only [Nat.add_zero] using hsum 0
  simp only [hsum, hsum0] at h
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  have h2_3 : m + 1 + 3 = m + 4 := by omega
  simp only [h2_2, h2_3] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 11 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 4, v 1 i = 11
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 31 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 4, v 2 i = 31
  simp only [v_2]; decide +kernel
lemma a_3 : a 3 = 85 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ i : Fin 4, v 3 i = 85
  simp only [v_3]; decide +kernel

noncomputable def cf (n : ℕ) : ℝ :=
  (-2 + (13 - 7 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n + (1 + Real.sqrt 3) ^ n * (13 + 7 * Real.sqrt 3)) / 6


theorem main_proof :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X - 2 * X ^ 2)) =
      X * (11 - 2 * X - 8 * X ^ 2)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (-2 + (13 - 7 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n + (1 + Real.sqrt 3) ^ n * (13 + 7 * Real.sqrt 3)) / 6) := by
  have hrec : ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X - 2 * X ^ 2)) =
      X * (11 - 2 * X - 8 * X ^ 2) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X - 2 * X ^ 2)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (11 - 2 * X - 8 * X ^ 2) : PowerSeries ℚ) =
        C (11 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 2 - C (8 : ℚ) * X ^ 3 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3] <;> try norm_num
    · have hq : (a n : ℚ) = 3 * a (n - 1) - 2 * a (n - 3) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      simp only [c1, c3, e1, e2, e3, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (-2 + (13 - 7 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n + (1 + Real.sqrt 3) ^ n * (13 + 7 * Real.sqrt 3)) / 6 := by
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hinv : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
      have hpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      field_simp
      nlinarith [hsq]
    have hb_1 : (a 1 : ℝ) = cf 1 := by
      rw [a_1]; unfold cf
      try simp only [div_eq_mul_inv, hinv]
      push_cast
      linear_combination ((-7 / 3 : ℝ)) * hsq
    have hb_2 : (a 2 : ℝ) = cf 2 := by
      rw [a_2]; unfold cf
      try simp only [div_eq_mul_inv, hinv]
      push_cast
      linear_combination ((-9 : ℝ)) * hsq
    have hb_3 : (a 3 : ℝ) = cf 3 := by
      rw [a_3]; unfold cf
      try simp only [div_eq_mul_inv, hinv]
      push_cast
      linear_combination ((-7 / 3 : ℝ) * Real.sqrt 3 ^ 2 + (-27 : ℝ)) * hsq
    have cf_rec : ∀ m : ℕ, cf (m + 4) = 3 * cf (m + 3) - 2 * cf (m + 1) := by
      intro m
      unfold cf
      have hp_m_1 : (1 - Real.sqrt 3) ^ (m + 2) = (1 - Real.sqrt 3) ^ (m + 1) * (1 - Real.sqrt 3) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_m_2 : (1 - Real.sqrt 3) ^ (m + 3) = (1 - Real.sqrt 3) ^ (m + 1) * (1 - Real.sqrt 3) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_m_3 : (1 - Real.sqrt 3) ^ (m + 4) = (1 - Real.sqrt 3) ^ (m + 1) * (1 - Real.sqrt 3) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      have hp_p_1 : (1 + Real.sqrt 3) ^ (m + 2) = (1 + Real.sqrt 3) ^ (m + 1) * (1 + Real.sqrt 3) ^ 1 := by
        rw [show m + 2 = (m + 1) + 1 by omega, pow_add]
      have hp_p_2 : (1 + Real.sqrt 3) ^ (m + 3) = (1 + Real.sqrt 3) ^ (m + 1) * (1 + Real.sqrt 3) ^ 2 := by
        rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
      have hp_p_3 : (1 + Real.sqrt 3) ^ (m + 4) = (1 + Real.sqrt 3) ^ (m + 1) * (1 + Real.sqrt 3) ^ 3 := by
        rw [show m + 4 = (m + 1) + 3 by omega, pow_add]
      simp only [hp_m_1, hp_m_2, hp_m_3, hp_p_1, hp_p_2, hp_p_3]
      generalize (1 - Real.sqrt 3) ^ (m + 1) = Xm
      generalize (1 + Real.sqrt 3) ^ (m + 1) = Xp
      try simp only [div_eq_mul_inv, hinv]
      push_cast
      linear_combination ((7 / 6 : ℝ) * Real.sqrt 3 ^ 2 * Xm + (7 / 6 : ℝ) * Real.sqrt 3 ^ 2 * Xp + (-13 / 6 : ℝ) * Real.sqrt 3 * Xm + (13 / 6 : ℝ) * Real.sqrt 3 * Xp) * hsq
    have hR : ∀ m : ℕ,
        (a (m + 1) : ℝ) = cf (m + 1) ∧
        (a (m + 2) : ℝ) = cf (m + 2) ∧
        (a (m + 3) : ℝ) = cf (m + 3) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_1, hb_2, hb_3⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 1 = m + 2 by omega] using h1), (by simpa only [show m + 1 + 2 = m + 3 by omega] using h2), ?_⟩
        rw [show m + 1 + 3 = m + 4 by omega]
        have hr : (a (m + 4) : ℝ) = 3 * a (m + 3) - 2 * a (m + 1) := by
          have h0' := hrec (m + 4) (by omega)
          simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 3 = m + 1 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h2, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 1)).1
    rw [show n - 1 + 1 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩

end OMA.P250461

theorem OMA.solution : type_of% @OMA.S_oeis_a250461.main := OMA.P250461.main_proof
