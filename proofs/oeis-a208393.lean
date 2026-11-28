import OMAStatements.S_oeis_a208393

open OMA.S_oeis_a208393 PowerSeries

namespace A208393Proof

abbrev Arr (n : ℕ) := Fin 2 → Fin n → Fin 3

-- The neighbour condition alone.
def NB {n : ℕ} (A : Arr n) : Prop := ∀ i j, numEqNeighbors A i j ≤ 2

instance {n : ℕ} (A : Arr n) : Decidable (NB A) := by unfold NB; infer_instance

def N3 (n : ℕ) : ℕ := (Finset.univ.filter fun A : Arr n => NB A).card

def relab (σ : Equiv.Perm (Fin 3)) {n : ℕ} (A : Arr n) : Arr n := fun i j => σ (A i j)

theorem nb_relab (σ : Equiv.Perm (Fin 3)) {n : ℕ} (A : Arr n) : NB (relab σ A) ↔ NB A := by
  simp only [NB, numEqNeighbors, LeftEq, UpEq, UpRightEq, relab, EmbeddingLike.apply_eq_iff_eq]

-- Restricted growth along a linear order.
def RG {L : Type} [LT L] (f : L → Fin 3) : Prop := ∀ p, ∀ v < f p, ∃ q < p, f q = v

theorem perm_cases : ∀ (σ : Equiv.Perm (Fin 3)) (x v : Fin 3), v < σ.symm x →
    (v = 0 ∧ x ≠ σ 0) ∨ (v = 1 ∧ x ≠ σ 0 ∧ x ≠ σ 1) := by
  decide +kernel

theorem fin3_one : ∀ x : Fin 3, x ≠ 0 → x ≠ 2 → x = 1 := by decide

theorem rg_iff {L : Type} [LinearOrder L] (f : L → Fin 3) (m0 m1 : L) (h0 : ∀ p, m0 ≤ p)
    (h1 : f m1 ≠ f m0) (h1m : ∀ p, f p ≠ f m0 → m1 ≤ p) (σ : Equiv.Perm (Fin 3)) :
    RG (fun p => σ.symm (f p)) ↔ σ 0 = f m0 ∧ σ 1 = f m1 := by
  constructor
  · intro H
    have hA : σ.symm (f m0) = 0 := by
      by_contra h
      obtain ⟨q, hq, _⟩ := H m0 0 (by
        rcases Fin.pos_iff_ne_zero.2 h with h'; exact h')
      exact absurd (h0 q) (not_le.2 hq)
    have e0 : σ 0 = f m0 := by rw [← hA]; simp
    refine ⟨e0, ?_⟩
    have hn0 : σ.symm (f m1) ≠ 0 := by
      intro h; apply h1; rw [← e0, ← h]; simp
    have hn2 : σ.symm (f m1) ≠ 2 := by
      intro h
      obtain ⟨q, hq, hq1⟩ := H m1 1 (by show 1 < σ.symm (f m1); rw [h]; decide)
      have : f q = σ 1 := by rw [← hq1]; simp
      have hne : f q ≠ f m0 := by
        rw [this, ← e0]; intro h'; exact absurd (σ.injective h') (by decide)
      exact absurd (h1m q hne) (not_le.2 hq)
    have := fin3_one _ hn0 hn2
    rw [← this]; simp
  · rintro ⟨e0, e1⟩ p v hv
    rcases perm_cases σ (f p) v hv with ⟨rfl, hp⟩ | ⟨rfl, hp0, hp1⟩
    · refine ⟨m0, lt_of_le_of_ne (h0 p) ?_, by show σ.symm (f m0) = 0; rw [← e0]; simp⟩
      rintro rfl; exact hp e0.symm
    · refine ⟨m1, lt_of_le_of_ne (h1m p (by rw [← e0]; exact hp0)) ?_, by show σ.symm (f m1) = 1; rw [← e1]; simp⟩
      rintro rfl; exact hp1 e1.symm

theorem card_perm01 : ∀ x y : Fin 3, x ≠ y →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ 0 = x ∧ σ 1 = y).card = 1 := by
  decide +kernel

def lin {n : ℕ} (A : Arr n) (p : Lex (Fin 2 × Fin n)) : Fin 3 := A (ofLex p).1 (ofLex p).2

theorem nv_iff {n : ℕ} (A : Arr n) : NewValuesInOrder A ↔ RG (lin A) := by
  constructor
  · intro h p v hv
    obtain ⟨i', j', hb, he⟩ := h (ofLex p).1 (ofLex p).2 v hv
    refine ⟨toLex (i', j'), ?_, he⟩
    have : p = toLex (ofLex p) := rfl
    rw [this, Prod.Lex.lt_iff]; exact hb
  · intro h i j v hv
    obtain ⟨q, hq, he⟩ := h (toLex (i, j)) v hv
    refine ⟨(ofLex q).1, (ofLex q).2, ?_, he⟩
    have : q = toLex (ofLex q) := rfl
    rw [this, Prod.Lex.lt_iff] at hq; exact hq

theorem relab_lin (σ : Equiv.Perm (Fin 3)) {n : ℕ} (A : Arr n) :
    lin (relab σ A) = fun p => σ (lin A p) := rfl

-- A neighbour-valid array with at least 3 columns is not constant.
theorem nonconst {n : ℕ} (hn : 3 ≤ n) (A : Arr n) (h : NB A) (c : Fin 3) :
    ∃ p, lin A p ≠ c := by
  by_contra hc
  push Not at hc
  have hA : ∀ i j, A i j = c := fun i j => hc (toLex (i, j))
  have := h 1 ⟨1, by omega⟩
  have h1 : LeftEq A 1 ⟨1, by omega⟩ := ⟨⟨0, by omega⟩, rfl, by rw [hA, hA]⟩
  have h2 : UpEq A 1 ⟨1, by omega⟩ := ⟨0, rfl, by rw [hA, hA]⟩
  have h3 : UpRightEq A 1 ⟨1, by omega⟩ := ⟨0, ⟨2, by omega⟩, rfl, rfl, by rw [hA, hA]⟩
  simp [numEqNeighbors, h1, h2, h3] at this

theorem one_relab {n : ℕ} (hn : 3 ≤ n) (B : Arr n) (h : NB B) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
      NewValuesInOrder (relab σ.symm B)).card = 1 := by
  have hne : (Finset.univ : Finset (Lex (Fin 2 × Fin n))).Nonempty :=
    ⟨toLex (0, ⟨0, by omega⟩), Finset.mem_univ _⟩
  set m0 := Finset.univ.min' hne
  have h0 : ∀ p, m0 ≤ p := fun p => Finset.min'_le _ _ (Finset.mem_univ p)
  have hne1 : (Finset.univ.filter fun p => lin B p ≠ lin B m0).Nonempty := by
    obtain ⟨p, hp⟩ := nonconst hn B h (lin B m0)
    exact ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩⟩
  set m1 := (Finset.univ.filter fun p => lin B p ≠ lin B m0).min' hne1
  have h1 : lin B m1 ≠ lin B m0 := (Finset.mem_filter.1 (Finset.min'_mem _ hne1)).2
  have h1m : ∀ p, lin B p ≠ lin B m0 → m1 ≤ p :=
    fun p hp => Finset.min'_le (Finset.univ.filter fun q => lin B q ≠ lin B m0) p
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩)
  rw [← card_perm01 (lin B m0) (lin B m1) h1.symm]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, nv_iff, relab_lin]
  exact rg_iff (lin B) m0 m1 h0 h1 h1m σ

def relabE (σ : Equiv.Perm (Fin 3)) (n : ℕ) : Arr n ≃ Arr n :=
  Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => σ

theorem N3_eq {n : ℕ} (hn : 3 ≤ n) : N3 n = 6 * a n := by
  have step1 : N3 n = ∑ B : Arr n, ∑ σ : Equiv.Perm (Fin 3),
      if NB B ∧ NewValuesInOrder (relab σ.symm B) then 1 else 0 := by
    rw [N3, Finset.card_filter]
    refine Finset.sum_congr rfl fun B _ => ?_
    by_cases hB : NB B
    · have := one_relab hn B hB
      rw [Finset.card_filter] at this
      simp only [hB, true_and, if_true]
      exact this.symm
    · simp [hB]
  rw [step1, Finset.sum_comm]
  have step2 : ∀ σ : Equiv.Perm (Fin 3), (∑ B : Arr n,
      if NB B ∧ NewValuesInOrder (relab σ.symm B) then 1 else 0) = a n := by
    intro σ
    rw [← (relabE σ n).sum_comp, a, Finset.card_filter]
    refine Finset.sum_congr rfl fun A _ => ?_
    have e : relab σ.symm ((relabE σ n) A) = A := by
      funext i j; simp [relab, relabE]
    have e2 : (relabE σ n) A = relab σ A := rfl
    have h3 := nb_relab σ A
    rw [e, e2]
    by_cases h1 : NB A <;> by_cases h2 : NewValuesInOrder A <;> simp_all [Valid, NB]
  simp only [step2, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rfl

abbrev Col := Fin 3 × Fin 3

-- Column scan: pb is the bottom entry of the previous column, pend is the value that the next
-- top entry must avoid.
def NBc (pb pend : Option (Fin 3)) {n : ℕ} (C : Fin n → Col) : Prop :=
  (∀ k : Fin n, k.val = 0 → pend ≠ some (C k).1) ∧
  ∀ j : Fin n, ¬ ((((j.val = 0 ∧ pb = some (C j).2) ∨
      ∃ j' : Fin n, j'.val + 1 = j.val ∧ (C j').2 = (C j).2) ∧ (C j).1 = (C j).2) ∧
    ∃ k : Fin n, k.val = j.val + 1 ∧ (C k).1 = (C j).2)

instance (pb pend : Option (Fin 3)) {n : ℕ} (C : Fin n → Col) : Decidable (NBc pb pend C) := by
  unfold NBc; infer_instance

def cols {n : ℕ} (A : Arr n) : Fin n → Col := fun j => (A 0 j, A 1 j)

theorem ite3 (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    ((if p then 1 else 0) + (if q then 1 else 0) + (if r then 1 else 0) ≤ 2) ↔
      ¬ (p ∧ q ∧ r) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

theorem nb_iff {n : ℕ} (A : Arr n) : NB A ↔ NBc none none (cols A) := by
  have h0 : ∀ j, numEqNeighbors A 0 j ≤ 2 := by
    intro j
    have u1 : ¬ UpEq A 0 j := by rintro ⟨i', h, _⟩; simp at h
    have u2 : ¬ UpRightEq A 0 j := by rintro ⟨i', j', h, _⟩; simp at h
    unfold numEqNeighbors
    simp only [u1, u2, if_false]
    split_ifs <;> omega
  have h1 : ∀ j, numEqNeighbors A 1 j ≤ 2 ↔
      ¬ (LeftEq A 1 j ∧ A 0 j = A 1 j ∧ ∃ k : Fin n, k.val = j.val + 1 ∧ A 0 k = A 1 j) := by
    intro j
    have u1 : UpEq A 1 j ↔ A 0 j = A 1 j := by
      constructor
      · rintro ⟨i', h, e⟩
        have : i' = 0 := Fin.ext (by simp at h; omega)
        subst this; exact e
      · intro e; exact ⟨0, rfl, e⟩
    have u2 : UpRightEq A 1 j ↔ ∃ k : Fin n, k.val = j.val + 1 ∧ A 0 k = A 1 j := by
      constructor
      · rintro ⟨i', k, h, hk, e⟩
        have : i' = 0 := Fin.ext (by simp at h; omega)
        subst this; exact ⟨k, hk, e⟩
      · rintro ⟨k, hk, e⟩; exact ⟨0, k, rfl, hk, e⟩
    unfold numEqNeighbors
    rw [ite3, u1, u2]
  unfold NB NBc
  rw [Fin.forall_fin_two]
  simp only [h0, implies_true, true_and, h1, cols, LeftEq]
  simp

def np (pb : Option (Fin 3)) (c : Col) : Option (Fin 3) :=
  if pb = some c.2 ∧ c.1 = c.2 then some c.2 else none

theorem nbc_cons (pb pend : Option (Fin 3)) {n : ℕ} (c : Col) (B : Fin n → Col) :
    NBc pb pend (Fin.cons c B : Fin (n + 1) → Col) ↔
      pend ≠ some c.1 ∧ NBc (some c.2) (np pb c) B := by
  unfold NBc np
  simp only [Fin.forall_fin_succ, Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ]
  by_cases h : pb = some c.2 ∧ c.1 = c.2
  · simp only [h, and_self, if_true]
    simp
    tauto
  · simp only [h, if_false]
    simp
    tauto

def G (pb pend : Option (Fin 3)) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun C : Fin n → Col => NBc pb pend C).card

theorem G_succ (pb pend : Option (Fin 3)) (n : ℕ) :
    G pb pend (n + 1) = ∑ c : Col, if pend ≠ some c.1 then G (some c.2) (np pb c) n else 0 := by
  rw [G, Finset.card_filter, ← (Fin.consEquiv fun _ => Col).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, nbc_cons]
  by_cases h : pend ≠ some c.1
  · rw [if_pos h, G, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h]
  · simp [h]

def cnt : ℕ → Option (Fin 3) → Option (Fin 3) → ℕ
  | 0, _, _ => 1
  | n + 1, pb, pend => ∑ c : Col, if pend ≠ some c.1 then cnt n (some c.2) (np pb c) else 0

theorem cnt_succ (n : ℕ) (pb pend : Option (Fin 3)) :
    cnt (n + 1) pb pend = ∑ c : Col, if pend ≠ some c.1 then cnt n (some c.2) (np pb c) else 0 := by
  rw [cnt]

theorem G_eq (n : ℕ) : ∀ pb pend, G pb pend n = cnt n pb pend := by
  induction n with
  | zero =>
    intro pb pend
    rw [G, Finset.filter_true_of_mem (fun C _ => ⟨fun k => k.elim0, fun k => k.elim0⟩)]
    simp [cnt]
  | succ n ih =>
    intro pb pend
    rw [G_succ, cnt_succ]
    simp only [ih]

def colsE (n : ℕ) : Arr n ≃ (Fin n → Col) where
  toFun := cols
  invFun C := fun i j => if i = 0 then (C j).1 else (C j).2
  left_inv A := by
    funext i j
    fin_cases i <;> rfl
  right_inv C := by
    funext j
    rfl

theorem N3_cnt (n : ℕ) : N3 n = cnt n none none := by
  rw [← G_eq, N3, G]
  refine Finset.card_equiv (colsE n) fun A => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact nb_iff A

def W (n : ℕ) (pb pend : Option (Fin 3)) : ℤ :=
  (cnt (n + 2) pb pend : ℤ) - 8 * cnt (n + 1) pb pend - 6 * cnt n pb pend

theorem W_succ (n : ℕ) (pb pend : Option (Fin 3)) :
    W (n + 1) pb pend =
      ∑ c : Col, if pend ≠ some c.1 then W n (some c.2) (np pb c) else 0 := by
  simp only [W, show n + 1 + 2 = n + 2 + 1 by ring]
  rw [cnt_succ (n + 2) pb pend, cnt_succ (n + 1) pb pend, cnt_succ n pb pend]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

theorem W_base : ∀ b : Fin 3, ∀ q : Option (Fin 3), (q = none ∨ q = some b) →
    W 0 (some b) q = 0 := by
  decide +kernel

theorem np_form (pb : Option (Fin 3)) (c : Col) : np pb c = none ∨ np pb c = some c.2 := by
  unfold np; split_ifs <;> simp

theorem W_zero (n : ℕ) : ∀ b q, (q = none ∨ q = some b) → W n (some b) q = 0 := by
  induction n with
  | zero => exact W_base
  | succ n ih =>
    intro b q hq
    rw [W_succ]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs
    · exact ih _ _ (np_form _ c)
    · rfl

theorem N3_rec (m : ℕ) : (N3 (m + 3) : ℤ) = 8 * N3 (m + 2) + 6 * N3 (m + 1) := by
  have h : W (m + 1) none none = 0 := by
    rw [W_succ]
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs
    · exact W_zero m _ _ (np_form _ c)
    · rfl
  simp only [W] at h
  rw [N3_cnt, N3_cnt, N3_cnt]
  linarith

theorem N3_1 : N3 1 = 9 := by rw [N3_cnt]; decide +kernel
theorem N3_2 : N3 2 = 81 := by rw [N3_cnt]; decide +kernel

theorem a1 : a 1 = 2 := by decide +kernel
theorem a2 : a 2 = 14 := by decide +kernel

theorem a3 : a 3 = 117 := by
  have h := N3_rec 0
  rw [N3_1, N3_2, N3_eq (le_refl 3)] at h
  push_cast at h
  omega

theorem a4 : a 4 = 1017 := by
  have h := N3_rec 1
  have h3 := N3_eq (le_refl 3)
  rw [a3] at h3
  rw [N3_2, h3, N3_eq (by norm_num : 3 ≤ 4)] at h
  push_cast at h
  omega

theorem a_rec (m : ℕ) : (a (m + 5) : ℤ) = 8 * a (m + 4) + 6 * a (m + 3) := by
  have h := N3_rec (m + 2)
  rw [N3_eq (by omega : 3 ≤ m + 2 + 3), N3_eq (by omega : 3 ≤ m + 2 + 2),
    N3_eq (by omega : 3 ≤ m + 2 + 1)] at h
  push_cast at h
  simp only [show m + 2 + 3 = m + 5 by ring, show m + 2 + 2 = m + 4 by ring,
    show m + 2 + 1 = m + 3 by ring] at h
  linarith

theorem gf :
    (1 - 8 * X - 6 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (1 + X) * (2 - 4 * X - 3 * X ^ 2) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 8 * X - 6 * X ^ 2) * s =
      s - (s * C (8 : ℤ)) * X ^ 1 - (s * C (6 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (1 + X) * (2 - 4 * X - 3 * X ^ 2) : PowerSeries ℤ) =
      C (2 : ℤ) * X ^ 1 - C (2 : ℤ) * X ^ 2 - C (7 : ℤ) * X ^ 3 - C (3 : ℤ) * X ^ 4 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · subst h; simp [a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := a_rec m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
    simp
    omega

noncomputable def R (n : ℕ) : ℝ :=
  ((4 - Real.sqrt 22) ^ n * (-2 + Real.sqrt 22) +
    (2 + Real.sqrt 22) * (4 + Real.sqrt 22) ^ n) / (8 * Real.sqrt 22)

theorem root_step (x : ℝ) (h : x ^ 2 = 8 * x + 6) (j : ℕ) :
    x ^ (j + 2) = 8 * x ^ (j + 1) + 6 * x ^ j := by
  linear_combination x ^ j * h

theorem R_rec (j : ℕ) : R (j + 2) = 8 * R (j + 1) + 6 * R j := by
  have hs : Real.sqrt 22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)
  have h1 := root_step (4 - Real.sqrt 22) (by linear_combination hs) j
  have h2 := root_step (4 + Real.sqrt 22) (by linear_combination hs) j
  unfold R
  rw [h1, h2]
  ring

theorem closed (m : ℕ) : (a (m + 3) : ℝ) = R (m + 3) ∧ (a (m + 4) : ℝ) = R (m + 4) := by
  have hs : Real.sqrt 22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a3, R, eq_div_iff (by positivity)]; push_cast
      linear_combination (-(28 * Real.sqrt 22)) * hs
    · rw [a4, R, eq_div_iff (by positivity)]; push_cast
      linear_combination (-(2 * Real.sqrt 22 ^ 3 + 300 * Real.sqrt 22)) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 5) : ℝ) = 8 * (a (m + 4) : ℝ) + 6 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 4 = m + 5 by ring, hr, show m + 5 = (m + 3) + 2 by ring, R_rec, h1, h2]

end A208393Proof

open A208393Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a208393.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact (closed m).1
