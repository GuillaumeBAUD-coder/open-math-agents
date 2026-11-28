import OMAStatements.S_oeis_a223322

open OMA.S_oeis_a223322
open Finset

private instance edgeDecidable : DecidableRel edge := fun u v =>
  inferInstanceAs (Decidable (v ∈ nbrs u))

private theorem edge_symm : ∀ u v : Fin 12, edge u v → edge v u := by decide +kernel

private def State := {p : Fin 12 × Fin 12 // edge p.1 p.2}

private def nextOK (u v : State) : Prop :=
  edge u.val.1 v.val.1 ∧ edge u.val.2 v.val.2

private instance nextDecidable : DecidableRel nextOK := fun u v =>
  inferInstanceAs (Decidable (edge u.val.1 v.val.1 ∧ edge u.val.2 v.val.2))

private def Initial := {s : State // edge 0 s.val.2}
private def Next (s : State) := {t : State // nextOK s t}
private def End (s : State) := {z : Fin 12 // edge s.val.1 z}

private instance : Fintype State := inferInstanceAs (Fintype {p : Fin 12 × Fin 12 // edge p.1 p.2})
private instance : Fintype Initial := inferInstanceAs (Fintype {s : State // edge 0 s.val.2})
private instance (s : State) : Fintype (Next s) :=
  inferInstanceAs (Fintype {t : State // nextOK s t})
private instance (s : State) : Fintype (End s) :=
  inferInstanceAs (Fintype {z : Fin 12 // edge s.val.1 z})

private theorem initial_card : Fintype.card Initial = 25 := by decide +kernel
private theorem next_card : ∀ s : State, Fintype.card (Next s) = 13 := by decide +kernel
private theorem end_card : ∀ s : State, Fintype.card (End s) = 5 := by decide +kernel

private def Walking (n : ℕ) (s : State) :=
  {f : Fin (n + 1) → State // f 0 = s ∧ ∀ i : Fin n, nextOK (f i.castSucc) (f i.succ)}

private instance (n : ℕ) (s : State) : Finite (Walking n s) := by
  unfold Walking
  infer_instance

private def walkingZero (s : State) : Walking 0 s ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨fun _ => s, rfl, Fin.elim0⟩
  left_inv f := Subtype.ext (funext fun i => by fin_cases i; exact f.prop.1.symm)
  right_inv := fun u => by cases u; rfl

private def walkingSucc (n : ℕ) (s : State) :
    Walking (n + 1) s ≃ Σ t : Next s, Walking n t.val where
  toFun f :=
    ⟨⟨f.val (Fin.succ 0), by simpa [f.prop.1] using f.prop.2 0⟩,
      ⟨Fin.tail f.val, rfl, fun i => by
        exact f.prop.2 i.succ⟩⟩
  invFun f :=
    ⟨Fin.cons s f.2.val, by simp, fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [f.2.prop.1] using f.1.prop
      · exact f.2.prop.2 j⟩
  left_inv f := Subtype.ext (funext fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using f.prop.1.symm
    · simp [Fin.tail])
  right_inv := fun ⟨t, f⟩ => by
    obtain ⟨t, ht⟩ := t
    obtain ⟨f, h0, hf⟩ := f
    change f 0 = t at h0
    subst t
    apply Sigma.ext
    · exact Subtype.ext (by simp)
    · apply heq_of_eq
      exact Subtype.ext (by simp)

private theorem walking_card (n : ℕ) (s : State) : Nat.card (Walking n s) = 13 ^ n := by
  induction n generalizing s with
  | zero => simp [Nat.card_congr (walkingZero s)]
  | succ n ih =>
    rw [Nat.card_congr (walkingSucc n s), Nat.card_sigma]
    simp [ih, next_card, pow_succ, mul_comm]

private def Started (n : ℕ) := Σ s : Initial, Walking n s.val
private def Completed (n : ℕ) := Σ w : Started n, End (w.2.val (Fin.last n))

private instance (n : ℕ) : Finite (Started n) := by
  unfold Started
  infer_instance

private theorem started_card (n : ℕ) : Nat.card (Started n) = 25 * 13 ^ n := by
  unfold Started
  rw [Nat.card_sigma]
  simp [walking_card, initial_card]

private theorem completed_card (n : ℕ) : Nat.card (Completed n) = 125 * 13 ^ n := by
  classical
  let := Fintype.ofFinite (Started n)
  unfold Completed
  rw [Nat.card_sigma]
  simp only [Nat.card_eq_fintype_card, end_card, sum_const, card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, started_card]
  simp only [Nat.cast_id]
  ring

private theorem good_iff {n : ℕ} (x : Fin 2 → Fin (n + 1) → Fin 12) :
    Good x ↔ x 0 0 = 0 ∧
      (∀ b : Fin 2, ∀ i : Fin n, edge (x b i.castSucc) (x b i.succ)) ∧
      (∀ i : Fin n, edge (x 1 i.castSucc) (x 0 i.succ)) := by
  constructor
  · intro ⟨h, h0⟩
    refine ⟨h0 (by omega), ?_, ?_⟩
    · intro b i
      exact h (b, i.castSucc) (b, i.succ) (Or.inl ⟨rfl, Or.inr rfl⟩)
    · intro i
      exact h (1, i.castSucc) (0, i.succ) (Or.inr
        ⟨by simp [Nat.add_comm], Or.inl rfl⟩)
  · rintro ⟨h₀, hrow, hdiag⟩
    refine ⟨?_, fun _ => h₀⟩
    have indexStep (i j : Fin (n + 1)) (h : (j : ℕ) = (i : ℕ) + 1) :
        ∃ k : Fin n, i = k.castSucc ∧ j = k.succ := by
      refine ⟨⟨i, by have := j.isLt; omega⟩, Fin.ext rfl, Fin.ext h⟩
    rintro ⟨p, i⟩ ⟨q, j⟩ (⟨h, hr⟩ | ⟨ha, hv⟩)
    · change p = q at h
      subst q
      rcases hr with h | h
      · obtain ⟨k, rfl, rfl⟩ := indexStep j i h
        exact edge_symm _ _ (hrow p k)
      · obtain ⟨k, rfl, rfl⟩ := indexStep i j h
        exact hrow p k
    · change (p : ℕ) + (i : ℕ) = (q : ℕ) + (j : ℕ) at ha
      change (p : ℕ) = (q : ℕ) + 1 ∨ (q : ℕ) = (p : ℕ) + 1 at hv
      fin_cases p <;> fin_cases q
      · simp at hv
      · obtain ⟨k, rfl, rfl⟩ := indexStep j i (by simpa [Nat.add_comm] using ha)
        exact edge_symm _ _ (hdiag k)
      · obtain ⟨k, rfl, rfl⟩ := indexStep i j (by simpa [Nat.add_comm] using ha.symm)
        exact hdiag k
      · simp at hv

private def arrayOne : {x : Fin 2 → Fin 1 → Fin 12 // Good x} ≃ Fin 12 where
  toFun x := x.val 1 0
  invFun z := ⟨![fun _ => 0, fun _ => z],
    (good_iff _).mpr ⟨rfl, fun _ i => Fin.elim0 i, fun i => Fin.elim0 i⟩⟩
  left_inv x := Subtype.ext (funext fun b => funext fun i => by
    fin_cases b <;> fin_cases i
    · exact ((good_iff _).mp x.prop).1.symm
    · rfl)
  right_inv _ := rfl

private theorem array_one : a 1 = 12 := by
  change Nat.card _ = _
  rw [Nat.card_congr arrayOne]
  simp

private def encode (n : ℕ) (x : {x : Fin 2 → Fin (n + 2) → Fin 12 // Good x}) :
    Completed n := by
  have hgood := (good_iff x.val).mp x.prop
  let states : Fin (n + 1) → State := fun i =>
    ⟨(x.val 1 i.castSucc, x.val 0 i.succ), hgood.2.2 i⟩
  refine ⟨⟨⟨states 0, ?_⟩, ⟨states, rfl, ?_⟩⟩, ⟨x.val 1 (Fin.last (n + 1)), ?_⟩⟩
  · simpa [states, hgood.1] using hgood.2.1 0 0
  · intro i
    change edge (x.val 1 i.castSucc.castSucc) (x.val 1 i.succ.castSucc) ∧
      edge (x.val 0 i.castSucc.succ) (x.val 0 i.succ.succ)
    exact ⟨hgood.2.1 1 i.castSucc, hgood.2.1 0 i.succ⟩
  · exact hgood.2.1 1 (Fin.last n)

private def decode (n : ℕ) (w : Completed n) :
    {x : Fin 2 → Fin (n + 2) → Fin 12 // Good x} := by
  let top : Fin (n + 2) → Fin 12 := Fin.cons 0 (fun i => (w.1.2.val i).val.2)
  let bottom : Fin (n + 2) → Fin 12 :=
    Fin.lastCases w.2.val (fun i => (w.1.2.val i).val.1)
  refine ⟨![top, bottom], (good_iff _).mpr ⟨rfl, ?_, ?_⟩⟩
  · intro b i
    fin_cases b
    · change edge (top i.castSucc) (top i.succ)
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [top, w.1.2.prop.1] using w.1.1.prop
      · exact (w.1.2.prop.2 j).2
    · change edge (bottom i.castSucc) (bottom i.succ)
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [bottom] using w.2.prop
      · rw [Fin.succ_castSucc]
        simpa only [bottom, Fin.lastCases_castSucc] using (w.1.2.prop.2 j).1
  · intro i
    change edge (bottom i.castSucc) (top i.succ)
    simpa [bottom, top] using (w.1.2.val i).prop

private def arraysEquiv (n : ℕ) :
    {x : Fin 2 → Fin (n + 2) → Fin 12 // Good x} ≃ Completed n where
  toFun := encode n
  invFun := decode n
  left_inv x := by
    apply Subtype.ext
    funext b i
    fin_cases b
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact ((good_iff _).mp x.prop).1.symm
      · simp [decode, encode]
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [decode, encode]
      · simp [decode, encode]
  right_inv w := by
    obtain ⟨⟨⟨s, hs⟩, ⟨f, h0, hf⟩⟩, ⟨z, hz⟩⟩ := w
    change f 0 = s at h0
    subst s
    have he : (encode n (decode n ⟨⟨⟨f 0, hs⟩, ⟨f, rfl, hf⟩⟩, ⟨z, hz⟩⟩)).1.2.val = f := by
      funext i
      apply Subtype.ext
      apply Prod.ext <;> simp [encode, decode]
    apply Sigma.ext
    · apply Sigma.ext
      · exact Subtype.ext (congrFun he 0)
      · refine (Subtype.heq_iff_coe_eq ?_).mpr he
        intro g
        simp only [← congrFun he 0]
        rfl
    · refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
      · intro k
        simp only [he]
      · simp [encode, decode]

private theorem arrays_two_add (n : ℕ) : a (n + 2) = 125 * 13 ^ n := by
  change Nat.card _ = _
  exact (Nat.card_congr (arraysEquiv n)).trans (completed_card n)
open PowerSeries in
private theorem array_series
    (array_one : OMA.S_oeis_a223322.a 1 = 12)
    (arrays_two_add : ∀ n : ℕ, OMA.S_oeis_a223322.a (n + 2) = 125 * 13 ^ n) :
    mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a223322.a n : ℚ)) =
      OMA.S_oeis_a223322.G := by
  let A := mk (fun n => if n = 0 then (0 : ℚ) else (OMA.S_oeis_a223322.a n : ℚ))
  have h12 : (12 : PowerSeries ℚ) = C (12 : ℚ) :=
    (map_natCast (C : ℚ →+* PowerSeries ℚ) 12).symm
  have h13 : (13 : PowerSeries ℚ) = C (13 : ℚ) :=
    (map_natCast (C : ℚ →+* PowerSeries ℚ) 13).symm
  have h31 : (31 : PowerSeries ℚ) = C (31 : ℚ) :=
    (map_natCast (C : ℚ →+* PowerSeries ℚ) 31).symm
  have hprod : A * (1 - 13 * X) = X * (12 - 31 * X) := by
    rw [mul_sub, mul_one, mul_sub, h12, h13, h31, ← mul_assoc, ← mul_assoc]
    ext n
    rcases n with _ | _ | _ | n
    · norm_num [A, coeff_zero_mul_X, coeff_mul_C]
    · norm_num [A, coeff_succ_mul_X, coeff_mul_C, array_one]
    · norm_num [A, coeff_succ_mul_X, coeff_mul_C, coeff_X, array_one, arrays_two_add 0]
    · have h1 := arrays_two_add n
      have h2 := arrays_two_add (n + 1)
      simp only [map_sub, coeff_succ_mul_X, coeff_mul_C, coeff_X, A, coeff_mk,
        Nat.succ_ne_zero, if_false]
      norm_num [h1, h2, pow_succ]
      split
      · omega
      · ring
  have hunit : (1 - 13 * X : PowerSeries ℚ).constantCoeff ≠ 0 := by simp
  calc
    A = A * (1 - 13 * X) * (1 - 13 * X)⁻¹ := by
      rw [mul_assoc, PowerSeries.mul_inv_cancel _ hunit, mul_one]
    _ = OMA.S_oeis_a223322.G := by rw [hprod, OMA.S_oeis_a223322.G]

theorem OMA.solution : type_of% @OMA.S_oeis_a223322.main := by
  refine ⟨?_, array_series array_one arrays_two_add, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 = (k + 1) + 2 by omega,
      arrays_two_add, arrays_two_add, pow_succ]
    ring
  · intro n hn
    nth_rw 1 [← Nat.sub_add_cancel (show 2 ≤ n by omega)]
    exact arrays_two_add (n - 2)
