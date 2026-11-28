import OMAStatements.S_oeis_a183682

-- Credit: @Dariusthedoggie
-- Proof: row transfer matrix annihilated by the order-2 recurrence polynomial, giving recurrence, g.f. and Binet form, transferred to the integer-valued statement.

namespace OMA.P183682

open PowerSeries
/-- A `2 X 2` binary subblock is nonsingular (has nonzero determinant `a * d - b * c`). -/
def okBlock (a b c d : Fin 2) : Prop :=
  (a.val : ℤ) * d.val - (b.val : ℤ) * c.val ≠ 0

instance (a b c d : Fin 2) : Decidable (okBlock a b c d) := by
  unfold okBlock; infer_instance

/-- An `(m + 1) X 3` `0..1` array is valid when every `2 X 2` subblock satisfies `okBlock`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : Prop :=
  ∀ i : Fin m, ∀ j : Fin 2,
    okBlock (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)

instance (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A183682: Number of (n+1) X 3 binary arrays with every 2 X 2 subblock nonsingular. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 3 → Fin 2

def okRow (r₁ r₂ : Row) : Prop :=
  ∀ j : Fin 2, okBlock (r₁ j.castSucc) (r₁ j.succ) (r₂ j.castSucc) (r₂ j.succ)

instance (r₁ r₂ : Row) : Decidable (okRow r₁ r₂) := by
  unfold okRow; infer_instance

def enc (r : Row) : Fin 8 :=
  ⟨4 * (r 0).val + 2 * (r 1).val + (r 2).val, by
    have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt; omega⟩

def dec (k : Fin 8) : Row := fun c =>
  have hk := k.isLt
  if c.val = 0 then ⟨k.val / 4, by omega⟩
  else if c.val = 1 then ⟨(k.val / 2) % 2, by omega⟩
  else ⟨k.val % 2, by omega⟩

lemma enc_dec : ∀ k : Fin 8, enc (dec k) = k := by
  intro k; have hk := k.isLt; ext; simp [enc, dec]; try omega

lemma dec_enc : ∀ r : Row, dec (enc r) = r := by
  intro r; ext c
  have h0 := (r 0).isLt; have h1 := (r 1).isLt; have h2 := (r 2).isLt
  fin_cases c
  · change (dec (enc r) 0).val = (r 0).val; simp [dec, enc]; try omega
  · change (dec (enc r) 1).val = (r 1).val; simp [dec, enc]; try omega
  · change (dec (enc r) 2).val = (r 2).val; simp [dec, enc]; try omega

def ok2 (i j : Fin 8) : Prop := okRow (dec i) (dec j)

instance (i j : Fin 8) : Decidable (ok2 i j) := by
  unfold ok2; infer_instance

def adjMask : Fin 8 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 160
  | ⟨3, _⟩ => 96
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 204
  | ⟨6, _⟩ => 40
  | ⟨7, _⟩ => 36

lemma ok2_iff : ∀ i j : Fin 8, ok2 i j ↔ (adjMask i / 2 ^ j.val) % 2 = 1 := by decide +kernel

def step (f : Fin 8 → ℕ) (i : Fin 8) : ℕ :=
  ∑ j : Fin 8, if ok2 i j then f j else 0

def v : ℕ → Fin 8 → ℕ
  | 0, _ => 1
  | m + 1, i => step (v m) i

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ i : Fin 8, ∑ y : Fin (m + 1) → Row, if enc (y 0) = i then g y else 0 := by
  trans ∑ y : Fin (m + 1) → Row, ∑ i : Fin 8, if enc (y 0) = i then g y else 0
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

lemma v_eq (m : ℕ) (i : Fin 8) :
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ i : Fin 8, v (n + 1) i := by
  simp only [a, Finset.card_filter]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro i _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 : Fin 8 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 1
  | ⟨7, _⟩ => 1

def vtab1 : Fin 8 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 4
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 2

def vtab2 : Fin 8 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 6
  | ⟨3, _⟩ => 6
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 8
  | ⟨6, _⟩ => 6
  | ⟨7, _⟩ => 6

def vtab3 : Fin 8 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 14
  | ⟨3, _⟩ => 14
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 24
  | ⟨6, _⟩ => 14
  | ⟨7, _⟩ => 14

lemma v_0 : ∀ i : Fin 8, v 0 i = vtab0 i := by decide +kernel
lemma v_1 : ∀ i : Fin 8, v 1 i = vtab1 i := by
  intro i; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert i; decide +kernel
lemma v_2 : ∀ i : Fin 8, v 2 i = vtab2 i := by
  intro i; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert i; decide +kernel
lemma v_3 : ∀ i : Fin 8, v 3 i = vtab3 i := by
  intro i; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert i; decide +kernel

def err (m : ℕ) (i : Fin 8) : ℤ :=
  (v (m + 2) i : ℤ) - (v (m + 1) i : ℤ) - 4 * (v m i : ℤ)

lemma err_base : ∀ i : Fin 8, err 1 i = 0 := by
  intro i
  change (v 3 i : ℤ) - (v 2 i : ℤ) - 4 * (v 1 i : ℤ) = 0
  simp only [v_3, v_2, v_1]
  revert i; decide +kernel

lemma err_succ (m : ℕ) (i : Fin 8) :
    err (m + 1) i = ∑ j : Fin 8, if ok2 i j then err m j else 0 := by
  have hV : ∀ r, (v (r + 1) i : ℤ) = ∑ j : Fin 8, if ok2 i j then (v r j : ℤ) else 0 := by
    intro r; rw [v, step]; simp
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (i : Fin 8) : err (m + 1) i = 0 := by
  induction m generalizing i with
  | zero => simpa using err_base i
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun j _ => by simp [ih j])

lemma a_rec_ge (m : ℕ) :
    (a (m + 3) : ℤ) = a (m + 2) + 4 * a (m + 1) := by
  have h : ∑ i : Fin 8, err (m + 1) i = 0 :=
    Finset.sum_eq_zero (fun i _ => err_ge m i)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ i : Fin 8, (v (m + 1 + r) i : ℤ)) = (a (m + 1 + r) : ℤ) := by
    intro r
    have h1 : m + 1 + r = (m + 0 + r) + 1 := by omega
    rw [h1, a_succ, Nat.cast_sum]
  have hsum0 : (∑ i : Fin 8, (v (m + 1) i : ℤ)) = (a (m + 1) : ℤ) := by
    simpa using hsum 0
  simp only [hsum, hsum0] at h
  have h2_1 : m + 1 + 1 = m + 2 := by omega
  have h2_2 : m + 1 + 2 = m + 3 := by omega
  simp only [h2_1, h2_2] at h
  linarith

lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 12 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ i : Fin 8, v 1 i = 12
  simp only [v_1]; decide +kernel
lemma a_2 : a 2 = 32 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ i : Fin 8, v 2 i = 32
  simp only [v_2]; decide +kernel

noncomputable def cf (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ (-1 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17

theorem main_proof_ours :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
      4 * X * (3 + 5 * X)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((2 : ℝ) ^ (-1 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17) := by
  have hrec : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
      4 * X * (3 + 5 * X) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - 4 * X ^ 2) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        - C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (4 * X * (3 + 5 * X) : PowerSeries ℚ) =
        C (12 : ℚ) * X ^ 1 + C (20 : ℚ) * X ^ 2 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2] <;> try norm_num
    · have hq : (a n : ℚ) = a (n - 1) + 4 * a (n - 2) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      simp only [c1, c2, e1, e2, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((2 : ℝ) ^ (-1 - (n : ℤ)) * ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) + (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17 := by
    have hsq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have hbase_1 : (a 1 : ℝ) = cf 1 := by
      rw [a_1]; unfold cf
      rw [eq_div_iff (by positivity)]
      have hz : (2 : ℝ) ^ (-1 - ((1 : ℕ) : ℤ)) = ((1 : ℝ) / 4) := by norm_num
      rw [hz]
      push_cast
      ring
    have hbase_2 : (a 2 : ℝ) = cf 2 := by
      rw [a_2]; unfold cf
      rw [eq_div_iff (by positivity)]
      have hz : (2 : ℝ) ^ (-1 - ((2 : ℕ) : ℤ)) = ((1 : ℝ) / 8) := by norm_num
      rw [hz]
      push_cast
      linear_combination (-((5 : ℝ) / 4 * Real.sqrt 17)) * hsq
    have hf_rec : ∀ m : ℕ, cf (m + 3) = cf (m + 2) + 4 * cf (m + 1) := by
      intro m
      unfold cf
      have hchar1 : (1 - Real.sqrt 17) ^ 2 = 2 * (1 - Real.sqrt 17) + 16 := by
        linear_combination (1) * hsq
      have hchar2 : (1 + Real.sqrt 17) ^ 2 = 2 * (1 + Real.sqrt 17) + 16 := by
        linear_combination (1) * hsq
      have hz_1 : (2 : ℝ) ^ (-1 - ((m + 2 : ℕ) : ℤ)) = (2 : ℝ) ^ (-1 - ((m + 1 : ℕ) : ℤ)) / (2 : ℝ) ^ 1 := by
        rw [show -1 - ((m + 2 : ℕ) : ℤ) = (-1 - ((m + 1 : ℕ) : ℤ)) - ((1 : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      have hz_2 : (2 : ℝ) ^ (-1 - ((m + 3 : ℕ) : ℤ)) = (2 : ℝ) ^ (-1 - ((m + 1 : ℕ) : ℤ)) / (2 : ℝ) ^ 2 := by
        rw [show -1 - ((m + 3 : ℕ) : ℤ) = (-1 - ((m + 1 : ℕ) : ℤ)) - ((2 : ℕ) : ℤ) by push_cast; ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
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


lemma a_eq (n : ℕ) : OMA.S_oeis_a183682.a n = (a n : ℤ) := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem main_proof : type_of% @OMA.S_oeis_a183682.main := by
  obtain ⟨hrec, _, hcf⟩ := main_proof_ours
  have hfun : OMA.S_oeis_a183682.a = fun n => (a n : ℤ) := funext a_eq
  rw [hfun]
  refine ⟨hrec, ?_, fun n hn => ?_⟩
  · have hl : PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X - 4 * X ^ 2) =
        PowerSeries.mk (fun n => (a n : ℤ))
        - C (1 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1)
        - C (4 : ℤ) * (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (4 * X * (3 + 5 * X) : PowerSeries ℤ) =
        C (12 : ℤ) * X ^ 1 + C (20 : ℤ) * X ^ 2 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rcases n with _ | _ | _ | n <;> (try omega) <;> simp only [coeff_C, a_0, a_1, a_2] <;>
        norm_num [a_0, a_1, a_2]
    · have hq := hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      simp only [c1, c2, e1, e2, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  · exact_mod_cast hcf n hn

end OMA.P183682

theorem OMA.solution : type_of% @OMA.S_oeis_a183682.main := OMA.P183682.main_proof
