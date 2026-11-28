import OMAStatements.S_oeis_a253225

-- Credit: @Dariusthedoggie
-- Proof: 8-state row transfer matrix annihilated by the recurrence polynomial, giving g.f. and closed form, bridged to the index-pair min/max encoding.

namespace OMA.P253225

open PowerSeries
/-- Diagonal minimum minus antidiagonal minimum of the `2 X 2` subblock with upper row `r`, lower row `s`
and columns `j, j + 1` (diagonal `r j, s (j+1)`, antidiagonal `r (j+1), s j`). -/
def dmin (r s : Fin 3 → Fin 2) (j : Fin 2) : ℤ :=
  ((min (r j.castSucc) (s j.succ)).val : ℤ) - ((min (r j.succ) (s j.castSucc)).val : ℤ)

/-- Diagonal maximum minus antidiagonal maximum of the same subblock. -/
def dmax (r s : Fin 3 → Fin 2) (j : Fin 2) : ℤ :=
  ((max (r j.castSucc) (s j.succ)).val : ℤ) - ((max (r j.succ) (s j.castSucc)).val : ℤ)

/-- `dmin` is nondecreasing horizontally: from the subblock in columns `0, 1` to the one in columns `1, 2`. -/
def okPair (r s : Fin 3 → Fin 2) : Prop := ∀ j : Fin 1, dmin r s j.castSucc ≤ dmin r s j.succ

instance (r s : Fin 3 → Fin 2) : Decidable (okPair r s) := by
  unfold okPair; infer_instance

/-- `dmax` is nondecreasing vertically: from the subblock on rows `(r, s)` to the one on rows `(s, t)`. -/
def okTriple (r s t : Fin 3 → Fin 2) : Prop := ∀ j : Fin 2, dmax r s j ≤ dmax s t j

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

/-- A253225: Number of (n+1) X (2+1) 0..1 arrays with every 2 X 2 subblock diagonal minimum minus antidiagonal minimum nondecreasing horizontally and diagonal maximum minus antidiagonal maximum nondecreasing vertically. -/
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
  | 0, 0 => 139
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 803158884352
  | 0, 5 => 0
  | 0, 6 => 71776119061217280
  | 0, 7 => 18374686479671623680
  | 1, 0 => 207
  | 1, 1 => 35328
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 1095216660480
  | 1, 5 => 186916976721920
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 34
  | 2, 1 => 0
  | 2, 2 => 13369344
  | 2, 3 => 3422552064
  | 2, 4 => 146028888064
  | 2, 5 => 0
  | 2, 6 => 71776119061217280
  | 2, 7 => 18374686479671623680
  | 3, 0 => 187
  | 3, 1 => 43520
  | 3, 2 => 0
  | 3, 3 => 3422552064
  | 3, 4 => 803158884352
  | 3, 5 => 186916976721920
  | 3, 6 => 71776119061217280
  | 3, 7 => 18374686479671623680
  | 4, 0 => 8
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 803158884352
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 12
  | 5, 1 => 2048
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 1095216660480
  | 5, 5 => 186916976721920
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 2
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 3422552064
  | 6, 4 => 146028888064
  | 6, 5 => 0
  | 6, 6 => 71776119061217280
  | 6, 7 => 18374686479671623680
  | 7, 0 => 139
  | 7, 1 => 35328
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 803158884352
  | 7, 5 => 186916976721920
  | 7, 6 => 0
  | 7, 7 => 18374686479671623680
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
  | 0, 1 => 1
  | 0, 2 => 1
  | 0, 3 => 1
  | 0, 4 => 1
  | 0, 5 => 1
  | 0, 6 => 1
  | 0, 7 => 1
  | 1, 0 => 1
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 1
  | 1, 5 => 1
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 1
  | 2, 1 => 1
  | 2, 2 => 1
  | 2, 3 => 1
  | 2, 4 => 1
  | 2, 5 => 1
  | 2, 6 => 1
  | 2, 7 => 1
  | 3, 0 => 1
  | 3, 1 => 1
  | 3, 2 => 0
  | 3, 3 => 1
  | 3, 4 => 1
  | 3, 5 => 1
  | 3, 6 => 1
  | 3, 7 => 1
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 1
  | 4, 5 => 1
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 1
  | 5, 1 => 1
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 1
  | 5, 5 => 1
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 1
  | 6, 2 => 0
  | 6, 3 => 1
  | 6, 4 => 1
  | 6, 5 => 1
  | 6, 6 => 1
  | 6, 7 => 1
  | 7, 0 => 1
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 1
  | 7, 5 => 1
  | 7, 6 => 0
  | 7, 7 => 1
  | _, _ => 0

def vtab1 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 4
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 4
  | 0, 5 => 0
  | 0, 6 => 7
  | 0, 7 => 5
  | 1, 0 => 6
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 4
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 2
  | 2, 1 => 0
  | 2, 2 => 4
  | 2, 3 => 3
  | 2, 4 => 2
  | 2, 5 => 0
  | 2, 6 => 7
  | 2, 7 => 5
  | 3, 0 => 6
  | 3, 1 => 2
  | 3, 2 => 0
  | 3, 3 => 3
  | 3, 4 => 4
  | 3, 5 => 2
  | 3, 6 => 7
  | 3, 7 => 5
  | 4, 0 => 1
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 4
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 2
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 4
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 1
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 3
  | 6, 4 => 2
  | 6, 5 => 0
  | 6, 6 => 7
  | 6, 7 => 5
  | 7, 0 => 4
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 4
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 5
  | _, _ => 0

def vtab2 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 9
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 18
  | 0, 7 => 16
  | 1, 0 => 16
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 5
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 19
  | 2, 3 => 15
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 18
  | 2, 7 => 16
  | 3, 0 => 13
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 15
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 18
  | 3, 7 => 16
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 5
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 15
  | 6, 4 => 0
  | 6, 5 => 0
  | 6, 6 => 18
  | 6, 7 => 16
  | 7, 0 => 9
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 16
  | _, _ => 0

def vtab3 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 25
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 49
  | 0, 7 => 33
  | 1, 0 => 43
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 5
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 68
  | 2, 3 => 49
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 49
  | 2, 7 => 33
  | 3, 0 => 30
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 49
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 49
  | 3, 7 => 33
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 5
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 49
  | 6, 4 => 0
  | 6, 5 => 0
  | 6, 6 => 49
  | 6, 7 => 33
  | 7, 0 => 25
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 33
  | _, _ => 0

def vtab4 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 58
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 131
  | 0, 7 => 66
  | 1, 0 => 107
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 5
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 199
  | 2, 3 => 131
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 131
  | 2, 7 => 66
  | 3, 0 => 63
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 131
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 131
  | 3, 7 => 66
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 5
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 131
  | 6, 4 => 0
  | 6, 5 => 0
  | 6, 6 => 131
  | 6, 7 => 66
  | 7, 0 => 58
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 66
  | _, _ => 0

def vtab5 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 124
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 328
  | 0, 7 => 132
  | 1, 0 => 255
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 5
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 527
  | 2, 3 => 328
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 328
  | 2, 7 => 132
  | 3, 0 => 129
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 328
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 328
  | 3, 7 => 132
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 5
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 328
  | 6, 4 => 0
  | 6, 5 => 0
  | 6, 6 => 328
  | 6, 7 => 132
  | 7, 0 => 124
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 132
  | _, _ => 0

def vtab6 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 256
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 788
  | 0, 7 => 264
  | 1, 0 => 584
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 5
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 1315
  | 2, 3 => 788
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 788
  | 2, 7 => 264
  | 3, 0 => 261
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 788
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 788
  | 3, 7 => 264
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 5
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 788
  | 6, 4 => 0
  | 6, 5 => 0
  | 6, 6 => 788
  | 6, 7 => 264
  | 7, 0 => 256
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 264
  | _, _ => 0

def vtab7 (p : Fin 8 × Fin 8) : ℕ := match p.1.val, p.2.val with
  | 0, 0 => 520
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 5
  | 0, 5 => 0
  | 0, 6 => 1840
  | 0, 7 => 528
  | 1, 0 => 1308
  | 1, 1 => 1
  | 1, 2 => 0
  | 1, 3 => 0
  | 1, 4 => 5
  | 1, 5 => 2
  | 1, 6 => 0
  | 1, 7 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 3155
  | 2, 3 => 1840
  | 2, 4 => 0
  | 2, 5 => 0
  | 2, 6 => 1840
  | 2, 7 => 528
  | 3, 0 => 525
  | 3, 1 => 3
  | 3, 2 => 0
  | 3, 3 => 1840
  | 3, 4 => 5
  | 3, 5 => 2
  | 3, 6 => 1840
  | 3, 7 => 528
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 0
  | 4, 3 => 0
  | 4, 4 => 5
  | 4, 5 => 0
  | 4, 6 => 0
  | 4, 7 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 5
  | 5, 5 => 2
  | 5, 6 => 0
  | 5, 7 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 0
  | 6, 3 => 1840
  | 6, 4 => 0
  | 6, 5 => 0
  | 6, 6 => 1840
  | 6, 7 => 528
  | 7, 0 => 520
  | 7, 1 => 1
  | 7, 2 => 0
  | 7, 3 => 0
  | 7, 4 => 5
  | 7, 5 => 2
  | 7, 6 => 0
  | 7, 7 => 528
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
lemma v_7 : ∀ p : Fin 8 × Fin 8, v 7 p = vtab7 p := by
  intro p; rw [show (7 : ℕ) = 6 + 1 from rfl, v, step]; simp only [v_6, ok2_iff]; revert p; decide +kernel

def err (m : ℕ) (p : Fin 8 × Fin 8) : ℤ :=
  (v (m + 3) p : ℤ) - 5 * (v (m + 2) p : ℤ) + 8 * (v (m + 1) p : ℤ) - 4 * (v m p : ℤ)

lemma err_base : ∀ p : Fin 8 × Fin 8, err 4 p = 0 := by
  intro p
  change (v 7 p : ℤ) - 5 * (v 6 p : ℤ) + 8 * (v 5 p : ℤ) - 4 * (v 4 p : ℤ) = 0
  simp only [v_7, v_6, v_5, v_4]
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

lemma err_ge (m : ℕ) (p : Fin 8 × Fin 8) : err (m + 4) p = 0 := by
  induction m generalizing p with
  | zero => simpa using err_base p
  | succ m ih =>
    rw [show m + 1 + 4 = (m + 4) + 1 by omega, err_succ]
    exact Finset.sum_eq_zero (fun q _ => by simp [ih q])

lemma a_rec_ge (m : ℕ) :
    (a (m + 8) : ℤ) = 5 * a (m + 7) - 8 * a (m + 6) + 4 * a (m + 5) := by
  have h : ∑ p : Fin 8 × Fin 8, err (m + 4) p = 0 :=
    Finset.sum_eq_zero (fun p _ => err_ge m p)
  unfold err at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hsum : ∀ r : ℕ, (∑ p : Fin 8 × Fin 8, (v (m + 4 + r) p : ℤ)) = (a (m + 4 + r + 1) : ℤ) := by
    intro r
    rw [a_succ, Nat.cast_sum]
  have hsum0 : (∑ p : Fin 8 × Fin 8, (v (m + 4) p : ℤ)) = (a (m + 4 + 1) : ℤ) := by
    rw [a_succ, Nat.cast_sum]
  simp only [hsum, hsum0] at h
  have h2_0 : m + 4 + 1 = m + 5 := by omega
  have h2_1 : m + 4 + 1 + 1 = m + 6 := by omega
  have h2_2 : m + 4 + 2 + 1 = m + 7 := by omega
  have h2_3 : m + 4 + 3 + 1 = m + 8 := by omega
  simp only [h2_0, h2_1, h2_2, h2_3] at h
  linarith


lemma a_0 : a 0 = 0 := rfl
lemma a_1 : a 1 = 47 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 0 p = 47
  simp only [v_0]; decide +kernel
lemma a_2 : a 2 = 132 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 1 p = 132
  simp only [v_1]; decide +kernel
lemma a_3 : a 3 = 306 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 2 p = 306
  simp only [v_2]; decide +kernel
lemma a_4 : a 4 = 742 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 3 p = 742
  simp only [v_3]; decide +kernel
lemma a_5 : a 5 = 1775 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 4 p = 1775
  simp only [v_4]; decide +kernel
lemma a_6 : a 6 = 4158 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 5 p = 4158
  simp only [v_5]; decide +kernel
lemma a_7 : a 7 = 9551 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, a_succ]
  change ∑ p : Fin 8 × Fin 8, v 6 p = 9551
  simp only [v_6]; decide +kernel

def cf (n : ℕ) : ℚ :=
  19 + 377 * (2 : ℚ) ^ ((n : ℤ) - 6) + 627 * (2 : ℚ) ^ ((n : ℤ) - 6) * (n : ℚ)


theorem main_proof_ours :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 4 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) ^ 2) =
      X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6)) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 19 + 377 * (2 : ℚ) ^ ((n : ℤ) - 6) + 627 * (2 : ℚ) ^ ((n : ℤ) - 6) * (n : ℚ)) := by
  have hrec : ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 5 * a (n - 1) - 8 * a (n - 2) + 4 * a (n - 3) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simpa using a_rec_ge m
  have hgf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) ^ 2) =
      X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) := by
    have hl : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) ^ 2) =
        PowerSeries.mk (fun n => (a n : ℚ))
        - C (5 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + C (8 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        - C (4 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by
      simp only [map_ofNat, map_one]; ring
    have hr : (X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) : PowerSeries ℚ) =
        C (47 : ℚ) * X ^ 1 - C (103 : ℚ) * X ^ 2 + C (22 : ℚ) * X ^ 3 + C (80 : ℚ) * X ^ 4 - C (15 : ℚ) * X ^ 5 - C (5 : ℚ) * X ^ 6 - C (7 : ℚ) * X ^ 7 := by
      simp only [map_ofNat, map_one]; ring
    rw [hl, hr]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge n 8 with hn | hn
    · interval_cases n <;> simp [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> try norm_num
    · have hq : (a n : ℚ) = 5 * a (n - 1) - 8 * a (n - 2) + 4 * a (n - 3) := by
        exact_mod_cast hrec n (by omega)
      have c1 : 1 ≤ n := by omega
      have c2 : 2 ≤ n := by omega
      have c3 : 3 ≤ n := by omega
      have e1 : n - 1 ≠ 0 := by omega
      have e2 : n - 2 ≠ 0 := by omega
      have e3 : n - 3 ≠ 0 := by omega
      have e4 : n - 4 ≠ 0 := by omega
      have e5 : n - 5 ≠ 0 := by omega
      have e6 : n - 6 ≠ 0 := by omega
      have e7 : n - 7 ≠ 0 := by omega
      simp only [c1, c2, c3, e1, e2, e3, e4, e5, e6, e7, coeff_C, if_true, if_false, ite_self]
      rw [hq]; ring
  have hcf : ∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 19 + 377 * (2 : ℚ) ^ ((n : ℤ) - 6) + 627 * (2 : ℚ) ^ ((n : ℤ) - 6) * (n : ℚ) := by
    have hb_5 : (a 5 : ℚ) = cf 5 := by
      rw [a_5]; unfold cf
      have hz_z : (2 : ℚ) ^ (((5 : ℕ) : ℤ) - 6) = (1 / 2 : ℚ) := by norm_num
      rw [hz_z]
      push_cast
      norm_num
    have hb_6 : (a 6 : ℚ) = cf 6 := by
      rw [a_6]; unfold cf
      have hz_z : (2 : ℚ) ^ (((6 : ℕ) : ℤ) - 6) = (1 : ℚ) := by norm_num
      rw [hz_z]
      push_cast
      norm_num
    have hb_7 : (a 7 : ℚ) = cf 7 := by
      rw [a_7]; unfold cf
      have hz_z : (2 : ℚ) ^ (((7 : ℕ) : ℤ) - 6) = (2 : ℚ) := by norm_num
      rw [hz_z]
      push_cast
      norm_num
    have cf_rec : ∀ m : ℕ, cf (m + 8) = 5 * cf (m + 7) - 8 * cf (m + 6) + 4 * cf (m + 5) := by
      intro m
      unfold cf
      have hp_z_1 : (2 : ℚ) ^ (((m + 6 : ℕ) : ℤ) - 6) = (2 : ℚ) ^ (((m + 5 : ℕ) : ℤ) - 6) * (2 : ℚ) ^ 1 := by
        rw [show ((m + 6 : ℕ) : ℤ) - 6 = (((m + 5 : ℕ) : ℤ) - 6) + ((1 : ℕ) : ℤ) by push_cast; ring, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      have hp_z_2 : (2 : ℚ) ^ (((m + 7 : ℕ) : ℤ) - 6) = (2 : ℚ) ^ (((m + 5 : ℕ) : ℤ) - 6) * (2 : ℚ) ^ 2 := by
        rw [show ((m + 7 : ℕ) : ℤ) - 6 = (((m + 5 : ℕ) : ℤ) - 6) + ((2 : ℕ) : ℤ) by push_cast; ring, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      have hp_z_3 : (2 : ℚ) ^ (((m + 8 : ℕ) : ℤ) - 6) = (2 : ℚ) ^ (((m + 5 : ℕ) : ℤ) - 6) * (2 : ℚ) ^ 3 := by
        rw [show ((m + 8 : ℕ) : ℤ) - 6 = (((m + 5 : ℕ) : ℤ) - 6) + ((3 : ℕ) : ℤ) by push_cast; ring, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
      simp only [hp_z_1, hp_z_2, hp_z_3]
      generalize (2 : ℚ) ^ (((m + 5 : ℕ) : ℤ) - 6) = Xz
      push_cast
      ring
    have hR : ∀ m : ℕ,
        (a (m + 5) : ℚ) = cf (m + 5) ∧
        (a (m + 6) : ℚ) = cf (m + 6) ∧
        (a (m + 7) : ℚ) = cf (m + 7) := by
      intro m
      induction m with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨hb_5, hb_6, hb_7⟩
      | succ m ih =>
        obtain ⟨h0, h1, h2⟩ := ih
        refine ⟨(by simpa only [show m + 1 + 5 = m + 6 by omega] using h1), (by simpa only [show m + 1 + 6 = m + 7 by omega] using h2), ?_⟩
        rw [show m + 1 + 7 = m + 8 by omega]
        have hr : (a (m + 8) : ℚ) = 5 * a (m + 7) - 8 * a (m + 6) + 4 * a (m + 5) := by
          have h0' := hrec (m + 8) (by omega)
          simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega] at h0'
          exact_mod_cast h0'
        rw [hr, h2, h1, h0, ← cf_rec m]
    intro n hn
    have h := (hR (n - 5)).1
    rw [show n - 5 + 5 = n by omega] at h
    exact h
  exact ⟨hrec, hgf, hcf⟩


lemma col3 : ∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 →
    j = 0 ∧ j' = 1 ∧ j'' = 2 := by decide

lemma col2 : ∀ j j' : Fin 3, j'.val = j.val + 1 → (j = 0 ∧ j' = 1) ∨ (j = 1 ∧ j' = 2) := by
  decide

lemma minC : ∀ p q : Fin 2, ((min p q).val : ℤ) = min (p.val : ℤ) (q.val : ℤ) := by decide
lemma maxC : ∀ p q : Fin 2, ((max p q).val : ℤ) = max (p.val : ℤ) (q.val : ℤ) := by decide

lemma pair_of {m : ℕ} (i i' : Fin (m + 1)) (hi : i'.val = i.val + 1) :
    ∃ k : Fin m, k.castSucc = i ∧ k.succ = i' :=
  ⟨⟨i.val, by have := i'.isLt; omega⟩, Fin.ext rfl, Fin.ext (by simp [hi])⟩

lemma valid_iff (m : ℕ) (x : Fin (m + 1) → Fin 3 → Fin 2) :
    ((∀ i i' : Fin (m + 1), i'.val = i.val + 1 →
      (∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 → (min ((x i j).val : ℤ) ((x i' j').val : ℤ) - min ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
              min ((x i j').val : ℤ) ((x i' j'').val : ℤ) - min ((x i j'').val : ℤ) ((x i' j').val : ℤ)))) ∧
    ∀ i i' i'' : Fin (m + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 3, j'.val = j.val + 1 → (max ((x i j).val : ℤ) ((x i' j').val : ℤ) - max ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
              max ((x i' j).val : ℤ) ((x i'' j').val : ℤ) - max ((x i' j').val : ℤ) ((x i'' j).val : ℤ)))) ↔
      isValid m x := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k j => ?_, fun k l hkl j => ?_⟩
    · fin_cases j
      have := h1 k.castSucc k.succ (by simp) 0 1 2 rfl rfl
      simp only [dmin, minC]
      exact this
    · have hl : (l.succ : Fin (m + 1)).val = (k.succ : Fin (m + 1)).val + 1 := by simp [hkl]
      simp only [dmax, maxC]
      fin_cases j
      · exact h2 k.castSucc k.succ l.succ (by simp) hl 0 1 rfl
      · exact h2 k.castSucc k.succ l.succ (by simp) hl 1 2 rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun i i' hi j j' j'' hj hj' => ?_, fun i i' i'' hi hi' j j' hj => ?_⟩
    · obtain ⟨k, rfl, rfl⟩ := pair_of i i' hi
      obtain ⟨rfl, rfl, rfl⟩ := col3 j j' j'' hj hj'
      have := h1 k 0
      simp only [dmin, minC] at this
      exact this
    · obtain ⟨k, rfl, rfl⟩ := pair_of i i' hi
      obtain ⟨l, hl1, rfl⟩ := pair_of _ i'' hi'
      have hkl : l.val = k.val + 1 := by
        have := congrArg Fin.val hl1; simp at this; omega
      rcases col2 j j' hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have := h2 k l hkl 0
        simp only [dmax, maxC] at this
        exact this
      · have := h2 k l hkl 1
        simp only [dmax, maxC] at this
        exact this

lemma a_eq (m : ℕ) : OMA.S_oeis_a253225.a (m + 1) = a (m + 1) := by
  unfold OMA.S_oeis_a253225.a
  show _ = (Finset.univ.filter (isValid (m + 1))).card
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact valid_iff (m + 1) x

theorem main_proof : type_of% @OMA.S_oeis_a253225.main := by
  obtain ⟨_, hgf, hcf⟩ := main_proof_ours
  have hser : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a253225.a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    cases n with
    | zero => simp [a]
    | succ m => simp [a_eq]
  refine ⟨by rw [hser]; exact hgf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_eq m]
  exact hcf (m + 1) (by omega)

end OMA.P253225

theorem OMA.solution : type_of% @OMA.S_oeis_a253225.main := OMA.P253225.main_proof
