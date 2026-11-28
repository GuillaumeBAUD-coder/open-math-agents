import OMAStatements.S_oeis_a206261

-- Credit: @Dariusthedoggie
-- Proof: 8-state row transfer matrix annihilated by the order-5 recurrence polynomial, giving g.f. and closed forms, bridged to the index-pair encoding.

namespace OMA.P206261

open PowerSeries
/-- Number of rightwards and downwards edge increases in the `2 X 2` subblock with upper row `r`,
lower row `s` and columns `j, j + 1`: the edges are `(r j, r (j+1))`, `(s j, s (j+1))` (rightwards) and
`(r j, s j)`, `(r (j+1), s (j+1))` (downwards). -/
def inc (r s : Fin 3 → Fin 2) (j : Fin 2) : ℕ :=
  (if r j.castSucc < r j.succ then 1 else 0) + (if s j.castSucc < s j.succ then 1 else 0) +
  (if r j.castSucc < s j.castSucc then 1 else 0) + (if r j.succ < s j.succ then 1 else 0)

/-- Horizontally neighboring subblocks (same pair of rows, columns `0, 1` and `1, 2`) have equal counts. -/
def okPair (r s : Fin 3 → Fin 2) : Prop := ∀ j : Fin 1, inc r s j.castSucc = inc r s j.succ

instance (r s : Fin 3 → Fin 2) : Decidable (okPair r s) := by
  unfold okPair; infer_instance

/-- Vertically neighboring subblocks (row pairs `(r, s)` and `(s, t)`, same columns) have equal counts. -/
def okTriple (r s t : Fin 3 → Fin 2) : Prop := ∀ j : Fin 2, inc r s j = inc s t j

instance (r s t : Fin 3 → Fin 2) : Decidable (okTriple r s t) := by
  unfold okTriple; infer_instance

/-- An `(m + 1) X 3` `0..1` array is valid when every pair of consecutive rows satisfies `okPair`
and, for consecutive row pairs `(i, i+1)` and `(j, j+1)` with `j = i + 1`, the rows `i, i+1, j+1`
satisfy `okTriple`. -/
def isValid (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : Prop :=
  (∀ i : Fin m, okPair (x i.castSucc) (x i.succ)) ∧
  (∀ i j : Fin m, j.val = i.val + 1 → okTriple (x i.castSucc) (x i.succ) (x j.succ))

instance (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) : Decidable (isValid m x) := by
  unfold isValid; infer_instance

/-- A206261: Number of (n+1) X 3 0..1 arrays with the number of rightwards and downwards edge increases in each 2 X 2 subblock equal to the number in all its horizontal and vertical neighbors. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (Finset.univ.filter (isValid (n + 1))).card

abbrev Row := Fin 3 → Fin 2

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

def ok2 (p q : Fin 8 × Fin 8) : Prop :=
  p.2 = q.1 ∧ okPair (dec p.1) (dec p.2) ∧ okTriple (dec p.1) (dec p.2) (dec q.2)

instance (p q : Fin 8 × Fin 8) : Decidable (ok2 p q) := by
  unfold ok2; infer_instance

def adjMask (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 2097152
  | 1, 3 => 0
  | 1, 4 => 274877906944
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 13194139533312
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 4096
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 73014444032
  | 4, 5 => 0
  | 4, 6 => 2251799813685248
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 2097152
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 33554432
  | 6, 4 => 73014444032
  | 6, 5 => 0
  | 6, 6 => 22799473113563136
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 73014444032
  | 7, 5 => 0
  | 7, 6 => 22799473113563136
  | 7, 7 => 15060037153926938624
  | _, _ => 0

lemma ok2_iff : ∀ p q : Fin 8 × Fin 8, ok2 p q ↔ (adjMask p / 2 ^ (8 * q.1.val + q.2.val)) % 2 = 1 := by decide +kernel

def step (f : Fin 8 × Fin 8 → ℕ) (p : Fin 8 × Fin 8) : ℕ :=
  ∑ q : Fin 8 × Fin 8, if ok2 p q then f q else 0

def v : ℕ → Fin 8 × Fin 8 → ℕ
  | 0, p => if okPair (dec p.1) (dec p.2) then 1 else 0
  | m + 1, p => step (v m) p

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ y : Fin (m + 1) → Row, f (Fin.cons r y) := by
  rw [← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_two (f : (Fin 2 → Row) → ℕ) :
    ∑ x, f x = ∑ r : Row, ∑ s : Row, f ![r, s] := by
  rw [← (piFinTwoEquiv fun _ => Row).symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber2 (m : ℕ) (g : (Fin (m + 1 + 1) → Row) → ℕ) :
    ∑ y, g y = ∑ p : Fin 8 × Fin 8, ∑ y : Fin (m + 1 + 1) → Row, if (enc (y 0), enc (y 1)) = p then g y else 0 := by
  trans ∑ y : Fin (m + 1 + 1) → Row, ∑ p : Fin 8 × Fin 8, if (enc (y 0), enc (y 1)) = p then g y else 0
  · apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (enc (y 0), enc (y 1))]
    · simp
    · intro p _ hp; simp [Ne.symm hp]
    · simp
  · exact Finset.sum_comm

lemma isValid_one (y : Fin 2 → Row) : isValid 1 y ↔ okPair (y 0) (y 1) := by
  unfold isValid
  constructor
  · rintro ⟨h1, _⟩
    simpa using h1 0
  · intro h
    refine ⟨fun i => ?_, fun i j hij => absurd hij (by have := i.isLt; have := j.isLt; omega)⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa using h

lemma isValid_cons (m : ℕ) (r : Row) (y : Fin (m + 1 + 1) → Row) :
    isValid (m + 1 + 1) (Fin.cons r y) ↔ okPair r (y 0) ∧ okTriple r (y 0) (y 1) ∧ isValid (m + 1) y := by
  unfold isValid
  constructor
  · rintro ⟨hp, ht⟩
    refine ⟨?_, ?_, fun i => ?_, fun i j hij => ?_⟩
    · have h0 := hp 0
      rwa [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] at h0
    · have h0 := ht 0 1 (by simp)
      rwa [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.cons_succ] at h0
    · have h1 := hp i.succ
      rwa [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ] at h1
    · have h1 := ht i.succ j.succ (by simp [Fin.val_succ, hij])
      rwa [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ] at h1
  · rintro ⟨hp0, ht0, hyp, hyt⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · refine Fin.cases ?_ (fun i' => ?_) i
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]; exact hp0
      · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]; exact hyp i'
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hj : j' = 0 := Fin.ext (by rw [Fin.val_succ, Fin.val_zero] at hij; rw [Fin.val_zero]; omega)
          subst hj
          rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, Fin.cons_succ, Fin.succ_zero_eq_one]
          exact ht0
      | succ i' =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
          exact hyt i' j' (by simpa [Fin.val_succ] using hij)

lemma pick1 (p : Fin 8 × Fin 8) (s t : Row) :
    (∑ r : Row, if (enc r, enc s) = p ∧ okPair r s ∧ okTriple r s t then 1 else 0) =
      if ok2 p (enc s, enc t) then 1 else 0 := by
  rw [Finset.sum_eq_single (dec p.1)]
  · unfold ok2
    simp only [enc_dec, dec_enc, Prod.ext_iff, true_and]
    by_cases hs : enc s = p.2
    · have hd : dec p.2 = s := by rw [← hs, dec_enc]
      simp [hs, hd]
    · have hs' : ¬ p.2 = enc s := fun h => hs h.symm
      simp [hs, hs']
  · intro r _ hr
    have hne : enc r ≠ p.1 := fun h => hr (by rw [← h, dec_enc])
    simp [Prod.ext_iff, hne]
  · simp

lemma pick0 (p : Fin 8 × Fin 8) :
    (∑ r : Row, ∑ s : Row, if (enc r, enc s) = p ∧ okPair r s then 1 else 0) =
      if okPair (dec p.1) (dec p.2) then 1 else 0 := by
  rw [Finset.sum_eq_single (dec p.1)]
  · rw [Finset.sum_eq_single (dec p.2)]
    · simp [enc_dec]
    · intro s _ hs
      have hne : enc s ≠ p.2 := fun h => hs (by rw [← h, dec_enc])
      simp [Prod.ext_iff, hne]
    · simp
  · intro r _ hr
    have hne : enc r ≠ p.1 := fun h => hr (by rw [← h, dec_enc])
    apply Finset.sum_eq_zero
    intro s _
    simp [Prod.ext_iff, hne]
  · simp

lemma v_eq (m : ℕ) (p : Fin 8 × Fin 8) :
    v m p = ∑ y : Fin (m + 1 + 1) → Row, if (enc (y 0), enc (y 1)) = p ∧ isValid (m + 1) y then 1 else 0 := by
  induction m generalizing p with
  | zero =>
    show (if okPair (dec p.1) (dec p.2) then 1 else 0) = ∑ y : Fin 2 → Row, if (enc (y 0), enc (y 1)) = p ∧ isValid 1 y then 1 else 0
    rw [sum_two, ← pick0]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    simp [isValid_one]
  | succ m ih =>
    rw [v, step, sum_cons]
    simp only [Fin.cons_zero, Fin.cons_one, isValid_cons]
    rw [Finset.sum_comm]
    have hL : ∀ y : Fin (m + 1 + 1) → Row,
        (∑ r : Row, if (enc r, enc (y 0)) = p ∧ okPair r (y 0) ∧ okTriple r (y 0) (y 1) ∧ isValid (m + 1) y then 1 else 0) =
          if ok2 p (enc (y 0), enc (y 1)) ∧ isValid (m + 1) y then 1 else 0 := by
      intro y
      by_cases hv : isValid (m + 1) y
      · simp only [hv, and_true]
        exact pick1 p (y 0) (y 1)
      · simp [hv]
    simp only [hL]
    rw [fiber2]
    apply Finset.sum_congr rfl
    intro q _
    rw [ih q]
    by_cases h : ok2 p q
    · simp only [h, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : (enc (y 0), enc (y 1)) = q
      · simp [hy, h]
      · simp [hy]
    · simp only [h, ↓reduceIte]
      symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : (enc (y 0), enc (y 1)) = q
      · simp [hy, h]
      · simp [hy]

lemma a_succ (n : ℕ) : a (n + 1) = ∑ p : Fin 8 × Fin 8, v n p := by
  simp only [a, Finset.card_filter]
  rw [fiber2]
  apply Finset.sum_congr rfl
  intro p _
  rw [v_eq]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> tauto

def vtab0 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 1
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 1
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 1
  | 1, 3 => 1
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 1
  | 1, 7 => 1
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 1
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 1
  | 4, 4 => 1
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 1
  | 5, 3 => 1
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 1
  | 6, 5 => 0
  | 6, 6 => 1
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 1
  | 7, 5 => 0
  | 7, 6 => 1
  | 7, 7 => 1
  | _, _ => 0

def vtab1 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 1
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 2
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 2
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 1
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 2
  | 6, 5 => 0
  | 6, 6 => 3
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 2
  | 7, 5 => 0
  | 7, 6 => 3
  | 7, 7 => 4
  | _, _ => 0

def vtab2 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 2
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 1
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 3
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 2
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 3
  | 6, 5 => 0
  | 6, 6 => 6
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 3
  | 7, 5 => 0
  | 7, 6 => 6
  | 7, 7 => 10
  | _, _ => 0

def vtab3 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 1
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 2
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 4
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 1
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 4
  | 6, 5 => 0
  | 6, 6 => 10
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 4
  | 7, 5 => 0
  | 7, 6 => 10
  | 7, 7 => 20
  | _, _ => 0

def vtab4 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 2
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 1
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 2
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 5
  | 6, 5 => 0
  | 6, 6 => 15
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 0
  | 7, 6 => 15
  | 7, 7 => 35
  | _, _ => 0

def vtab5 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 1
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 2
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 6
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 1
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 6
  | 6, 5 => 0
  | 6, 6 => 21
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 6
  | 7, 5 => 0
  | 7, 6 => 21
  | 7, 7 => 56
  | _, _ => 0

def vtab6 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => 0
  | 0, 6 => 0
  | 0, 7 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 2
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 0
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 0
  | 2, 4 => 0
  | 2, 5 => 1
  | 2, 6 => 0
  | 2, 7 => 0
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 0
  | 3, 4 => 0
  | 3, 5 => 0
  | 3, 6 => 0
  | 3, 7 => 0
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 7
  | 4, 5 => 0
  | 4, 6 => 1
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 2
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 5 => 0
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 7
  | 6, 5 => 0
  | 6, 6 => 28
  | 6, 7 => 0
  | 7, 0 => 1
  | 7, 1 => 0
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 7
  | 7, 5 => 0
  | 7, 6 => 28
  | 7, 7 => 84
  | _, _ => 0

lemma v_0 : ∀ p : Fin 8 × Fin 8, v 0 p = vtab0 p := by decide +kernel
lemma v_1 : ∀ p : Fin 8 × Fin 8, v 1 p = vtab1 p := by
  intro p; rw [show (1 : ℕ) = 0 + 1 from rfl, v, step]; simp only [v_0, ok2_iff]; revert p; decide +kernel
lemma v_2 : ∀ p : Fin 8 × Fin 8, v 2 p = vtab2 p := by
  intro p; rw [show (2 : ℕ) = 1 + 1 from rfl, v, step]; simp only [v_1, ok2_iff]; revert p; decide +kernel
lemma v_3 : ∀ p : Fin 8 × Fin 8, v 3 p = vtab3 p := by
  intro p; rw [show (3 : ℕ) = 2 + 1 from rfl, v, step]; simp only [v_2, ok2_iff]; revert p; decide +kernel
lemma v_4 : ∀ p : Fin 8 × Fin 8, v 4 p = vtab4 p := by
  intro p; rw [show (4 : ℕ) = 3 + 1 from rfl, v, step]; simp only [v_3, ok2_iff]; revert p; decide +kernel
lemma v_5 : ∀ p : Fin 8 × Fin 8, v 5 p = vtab5 p := by
  intro p; rw [show (5 : ℕ) = 4 + 1 from rfl, v, step]; simp only [v_4, ok2_iff]; revert p; decide +kernel
lemma v_6 : ∀ p : Fin 8 × Fin 8, v 6 p = vtab6 p := by
  intro p; rw [show (6 : ℕ) = 5 + 1 from rfl, v, step]; simp only [v_5, ok2_iff]; revert p; decide +kernel

def err (m : ℕ) (p : Fin 8 × Fin 8) : ℤ :=
  (v (m + 5) p : ℤ) - 3 * (v (m + 4) p : ℤ) + 2 * (v (m + 3) p : ℤ) + 2 * (v (m + 2) p : ℤ) - 3 * (v (m + 1) p : ℤ) + (v m p : ℤ)

lemma err_base : ∀ p : Fin 8 × Fin 8, err 1 p = 0 := by
  intro p
  change (v 6 p : ℤ) - 3 * (v 5 p : ℤ) + 2 * (v 4 p : ℤ) + 2 * (v 3 p : ℤ) - 3 * (v 2 p : ℤ) + (v 1 p : ℤ) = 0
  simp only [v_6, v_5, v_4, v_3, v_2, v_1]
  revert p; decide +kernel

lemma err_succ (m : ℕ) (p : Fin 8 × Fin 8) :
    err (m + 1) p = ∑ q : Fin 8 × Fin 8, if ok2 p q then err m q else 0 := by
  have hV : ∀ r, (v (r + 1) p : ℤ) = ∑ q : Fin 8 × Fin 8, if ok2 p q then (v r q : ℤ) else 0 := by
    intro r; rw [v, step]; simp only [Nat.cast_sum, apply_ite Nat.cast, Nat.cast_zero]
  unfold err
  simp only [hV]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> ring

lemma err_ge (m : ℕ) (p : Fin 8 × Fin 8) : err (m + 1) p = 0 := by
  induction m generalizing p with
  | zero => simpa using err_base p
  | succ m ih =>
    rw [show m + 1 + 1 = (m + 1) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun q _ => by simp [ih q])

lemma a_rec_ge (m : ℕ) :
    (a (m + 7) : ℤ) = 3 * a (m + 6) - 2 * a (m + 5) - 2 * a (m + 4) + 3 * a (m + 3) - a (m + 2) := by
  have h : ∑ p : Fin 8 × Fin 8, err (m + 1) p = 0 :=
    Finset.sum_eq_zero (fun p _ => err_ge m p)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ p : Fin 8 × Fin 8, (v (m + 1 + r) p : ℤ)) = (a (m + 1 + r + 1) : ℤ) := by
    intro r
    rw [a_succ, Nat.cast_sum]
  have hsum0 : (∑ p : Fin 8 × Fin 8, (v (m + 1) p : ℤ)) = (a (m + 1 + 1) : ℤ) := by
    rw [a_succ, Nat.cast_sum]
  simp only [hsum, hsum0] at h
  have h2_0 : m + 1 + 1 = m + 2 := by omega
  have h2_1 : m + 1 + 1 + 1 = m + 3 := by omega
  have h2_2 : m + 1 + 2 + 1 = m + 4 := by omega
  have h2_3 : m + 1 + 3 + 1 = m + 5 := by omega
  have h2_4 : m + 1 + 4 + 1 = m + 6 := by omega
  have h2_5 : m + 1 + 5 + 1 = m + 7 := by omega
  simp only [h2_0, h2_1, h2_2, h2_3, h2_4, h2_5] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 24 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 0 p = 24
  simp only [v_0]; decide +kernel
lemma a_2 : a 2 = 28 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 1 p = 28
  simp only [v_1]; decide +kernel
lemma a_3 : a 3 = 44 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 2 p = 44
  simp only [v_2]; decide +kernel
lemma a_4 : a 4 = 64 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 3 p = 64
  simp only [v_3]; decide +kernel
lemma a_5 : a 5 = 93 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 4 p = 93
  simp only [v_4]; decide +kernel
lemma a_6 : a 6 = 128 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 5 p = 128
  simp only [v_5]; decide +kernel

def cfC (n : ℕ) : ℚ :=
  (((72 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) * (1 + (-1 : ℚ) ^ n) + ((78 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) * (1 - (-1 : ℚ) ^ n)) / 2


theorem main_proof_ours :
    (∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) + 3 * a (n - 4) - a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X)) =
      X * (24 - 44 * X + 8 * X ^ 2 + 36 * X ^ 3 - 27 * X ^ 4 + 5 * X ^ 5)) ∧
    (∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = (72 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = (78 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) := by
  have hrec : ∀ n : ℕ, 7 ≤ n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) + 3 * a (n - 4) - a (n - 5) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X)) =
      X * (24 - 44 * X + 8 * X ^ 2 + 36 * X ^ 3 - 27 * X ^ 4 + 5 * X ^ 5) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X)) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3)
        - C (3 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 4)
        + C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 5) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (24 - 44 * X + 8 * X ^ 2 + 36 * X ^ 3 - 27 * X ^ 4 + 5 * X ^ 5) : PowerSeries ℚ) =
        C (24 : ℚ) * X ^ 1 - C (44 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 + C (36 : ℚ) * X ^ 4 - C (27 : ℚ) * X ^ 5 + C (5 : ℚ) * X ^ 6 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 7 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6] <;> try norm_num
    · have hq : (a n : ℚ) = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) + 3 * a (n - 4) - a (n - 5) := by
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
      have e6 : n - 6 ≠ 0 := by omega
      simp only [c1, c2, c3, c4, c5, e1, e2, e3, e4, e5, e6, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcfC : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (((72 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) * (1 + (-1 : ℚ) ^ n) + ((78 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) * (1 - (-1 : ℚ) ^ n)) / 2 := by
    have hb_2 : (a 2 : ℚ) = cfC 2 := by
      rw [a_2]; unfold cfC
      push_cast
      norm_num
    have hb_3 : (a 3 : ℚ) = cfC 3 := by
      rw [a_3]; unfold cfC
      push_cast
      norm_num
    have hb_4 : (a 4 : ℚ) = cfC 4 := by
      rw [a_4]; unfold cfC
      push_cast
      norm_num
    have hb_5 : (a 5 : ℚ) = cfC 5 := by
      rw [a_5]; unfold cfC
      push_cast
      norm_num
    have hb_6 : (a 6 : ℚ) = cfC 6 := by
      rw [a_6]; unfold cfC
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cfC (m + 7) = 3 * cfC (m + 6) - 2 * cfC (m + 5) - 2 * cfC (m + 4) + 3 * cfC (m + 3) - cfC (m + 2) := by
      intro m
      unfold cfC
      have hp_sg_1 : (-1 : ℚ) ^ (m + 3) = (-1 : ℚ) ^ (m + 2) * (-1 : ℚ) ^ 1 := by
        rw [show m + 3 = (m + 2) + 1 by omega, pow_add]
      have hp_sg_2 : (-1 : ℚ) ^ (m + 4) = (-1 : ℚ) ^ (m + 2) * (-1 : ℚ) ^ 2 := by
        rw [show m + 4 = (m + 2) + 2 by omega, pow_add]
      have hp_sg_3 : (-1 : ℚ) ^ (m + 5) = (-1 : ℚ) ^ (m + 2) * (-1 : ℚ) ^ 3 := by
        rw [show m + 5 = (m + 2) + 3 by omega, pow_add]
      have hp_sg_4 : (-1 : ℚ) ^ (m + 6) = (-1 : ℚ) ^ (m + 2) * (-1 : ℚ) ^ 4 := by
        rw [show m + 6 = (m + 2) + 4 by omega, pow_add]
      have hp_sg_5 : (-1 : ℚ) ^ (m + 7) = (-1 : ℚ) ^ (m + 2) * (-1 : ℚ) ^ 5 := by
        rw [show m + 7 = (m + 2) + 5 by omega, pow_add]
      simp only [hp_sg_1, hp_sg_2, hp_sg_3, hp_sg_4, hp_sg_5]
      generalize (-1 : ℚ) ^ (m + 2) = Xsg
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 2) : ℚ) = cfC (m + 2) ∧
        (a (m + 3) : ℚ) = cfC (m + 3) ∧
        (a (m + 4) : ℚ) = cfC (m + 4) ∧
        (a (m + 5) : ℚ) = cfC (m + 5) ∧
        (a (m + 6) : ℚ) = cfC (m + 6) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_2, hb_3, hb_4, hb_5, hb_6⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2, h3, h4⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 2 = m + 3 by omega] using h1), (by simpa only [show m + 1 + 3 = m + 4 by omega] using h2), (by simpa only [show m + 1 + 4 = m + 5 by omega] using h3), (by simpa only [show m + 1 + 5 = m + 6 by omega] using h4), ?_⟩
        rw [show m + 1 + 6 = m + 7 by omega]
        have hr : (a (m + 7) : ℚ) = 3 * a (m + 6) - 2 * a (m + 5) - 2 * a (m + 4) + 3 * a (m + 3) - a (m + 2) := by
          have h0' := hrec (m + 7) (by omega)
          simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h4, h3, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 2)).1
    rw [show n - 2 + 2 = n by omega] at h
    exact h
  have hcfE : ∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = (72 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6 := by
    intro n hn he
    rw [hcfC n hn, he.neg_one_pow]
    ring
  have hcfO : ∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = (78 + 26 * (n : ℚ) + 9 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6 := by
    intro n hn ho
    rw [hcfC n hn, ho.neg_one_pow]
    ring
  exact ⟨hrec, hgf, hcfE, hcfO⟩


lemma col3 : ∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 →
    j = 0 ∧ j' = 1 ∧ j'' = 2 := by decide

lemma col2 : ∀ j j' : Fin 3, j'.val = j.val + 1 → (j = 0 ∧ j' = 1) ∨ (j = 1 ∧ j' = 2) := by
  decide

lemma pair_of {m : ℕ} (i i' : Fin (m + 1)) (hi : i'.val = i.val + 1) :
    ∃ k : Fin m, k.castSucc = i ∧ k.succ = i' :=
  ⟨⟨i.val, by have := i'.isLt; omega⟩, Fin.ext rfl, Fin.ext (by simp [hi])⟩

lemma valid_iff (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) :
    ((∀ i i' : Fin (m + 1), i'.val = i.val + 1 →
      (∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 →
        OMA.S_oeis_a206261.incr (x i j) (x i j') (x i' j) (x i' j') =
          OMA.S_oeis_a206261.incr (x i j') (x i j'') (x i' j') (x i' j''))) ∧
    ∀ i i' i'' : Fin (m + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 3, j'.val = j.val + 1 →
        OMA.S_oeis_a206261.incr (x i j) (x i j') (x i' j) (x i' j') =
          OMA.S_oeis_a206261.incr (x i' j) (x i' j') (x i'' j) (x i'' j'))) ↔ isValid m x := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k j => ?_, fun k l hkl j => ?_⟩
    · fin_cases j
      exact h1 k.castSucc k.succ (by simp) 0 1 2 rfl rfl
    · have hl : (l.succ : Fin (m + 1)).val = (k.succ : Fin (m + 1)).val + 1 := by simp [hkl]
      fin_cases j
      · exact h2 k.castSucc k.succ l.succ (by simp) hl 0 1 rfl
      · exact h2 k.castSucc k.succ l.succ (by simp) hl 1 2 rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun i i' hi j j' j'' hj hj' => ?_, fun i i' i'' hi hi' j j' hj => ?_⟩
    · obtain ⟨k, rfl, rfl⟩ := pair_of i i' hi
      obtain ⟨rfl, rfl, rfl⟩ := col3 j j' j'' hj hj'
      exact h1 k 0
    · obtain ⟨k, rfl, rfl⟩ := pair_of i i' hi
      obtain ⟨l, hl1, rfl⟩ := pair_of _ i'' hi'
      have hkl : l.val = k.val + 1 := by
        have := congrArg Fin.val hl1; simp at this; omega
      rcases col2 j j' hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h2 k l hkl 0
      · exact h2 k l hkl 1

lemma a_eq (m : ℕ) : OMA.S_oeis_a206261.a (m + 1) = a (m + 1) := by
  unfold OMA.S_oeis_a206261.a
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact valid_iff (m + 1) x

theorem main_proof : type_of% @OMA.S_oeis_a206261.main := by
  obtain ⟨_, hgf, hev, hod⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a206261.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  have hA : ∀ n : ℕ, 1 < n → OMA.S_oeis_a206261.a n = a n := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_eq m
  refine ⟨by rw [hser]; exact hgf, fun n hn h2 => ?_, fun n hn h2 => ?_⟩
  · rw [hA n hn]; exact hev n hn (Nat.even_iff.mpr h2)
  · rw [hA n hn]; exact hod n hn (Nat.odd_iff.mpr h2)

end OMA.P206261

theorem OMA.solution : type_of% @OMA.S_oeis_a206261.main := OMA.P206261.main_proof
